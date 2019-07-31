// TODO: wait for io stabilization and completely rewrite it
use std::{fs, io, path, str};
use std::io::{Seek, SeekFrom};
use std::collections::{HashMap, HashSet};
use flate2::read::GzDecoder;
use crate::sat::formula::{Lit, Var, VarMap};
use crate::sat::{SolveRes, Solver};


pub fn write<W: io::Write, S: Solver>(_: W, _: &S) -> io::Result<()> {
    // TODO: implement
    unimplemented!()
}


pub fn parse_file<P: AsRef<path::Path>, S: Solver>(
    path: P,
    solver: &mut S,
    validate: bool,
) -> io::Result<VarMap<i32>> {
    let mut reader = io::BufReader::new(fs::File::open(path)?);
    {
        let gz = GzDecoder::new(&mut reader);

        if gz.header().is_some() {
            return parse(gz, solver, validate);
        }
    }

    reader.seek(SeekFrom::Start(0))?;
    parse(reader, solver, validate)
}


pub fn parse<R: io::Read, S: Solver>(
    reader: R,
    solver: &mut S,
    validate: bool,
) -> io::Result<VarMap<i32>> {
    let mut subst = Subst::new(solver);
    DimacsParser::parse(reader, validate, |cl| subst.add_clause(cl))?;
    Ok(subst.backward_subst)
}


pub fn write_result<W: io::Write, S>(
    mut writer: W,
    result: SolveRes<S>,
    backward_subst: &VarMap<i32>,
) -> io::Result<()> {
    match result {
        SolveRes::UnSAT(_) => {
            writeln!(writer, "UNSAT")?;
        }

        SolveRes::Interrupted(_, _) => {
            writeln!(writer, "INDET")?;
        }

        SolveRes::SAT(model, _) => {
            writeln!(writer, "SAT")?;
            for lit in model.iter() {
                let var_id = backward_subst[&lit.var()];
                write!(writer, "{} ", if lit.sign() { -var_id } else { var_id })?;
            }
            writeln!(writer, "0")?;
        }
    }
    Ok(())
}


pub fn validate_model_file<P: AsRef<path::Path>>(
    path: P,
    backward_subst: &VarMap<i32>,
    model: &Vec<Lit>,
) -> io::Result<bool> {
    let mut reader = io::BufReader::new(fs::File::open(path)?);
    {
        let gz = GzDecoder::new(&mut reader);
        if gz.header().is_some() {
            return validate_model(gz, backward_subst, model);
        }
    }

    reader.seek(SeekFrom::Start(0))?;
    validate_model(reader, backward_subst, model)
}

pub fn validate_model<R: io::Read>(
    reader: R,
    backward_subst: &VarMap<i32>,
    model: &Vec<Lit>,
) -> io::Result<bool> {
    let mut lits = HashSet::new();
    for lit in model.iter() {
        let lit_id = {
            let var_id = backward_subst[&lit.var()];
            if lit.sign() {
                -var_id
            } else {
                var_id
            }
        };

        lits.insert(lit_id);
        if lits.contains(&(-lit_id)) {
            return Ok(false);
        }
    }

    let mut ok = true;
    DimacsParser::parse(reader, false, |cl| {
        let mut found = false;
        for lit in cl {
            if lits.contains(&lit) {
                found = true;
                break;
            }
        }

        if !found {
            ok = false;
        }
    })?;

    Ok(ok)
}


struct Subst<'s, S: 's> {
    solver: &'s mut S,
    forward_subst: HashMap<i32, Var>,
    backward_subst: VarMap<i32>,
}

impl<'s, S: Solver> Subst<'s, S> {
    pub fn new(solver: &'s mut S) -> Self {
        Subst {
            solver,
            forward_subst: HashMap::new(),
            backward_subst: VarMap::new(),
        }
    }

    pub fn add_clause(&mut self, raw: Vec<i32>) {
        let lits: Vec<Lit> = raw.iter().map(|&lit_id| self.lit_by_id(lit_id)).collect();
        self.solver.add_clause(&lits[..]);
    }

    fn lit_by_id(&mut self, lit_id: i32) -> Lit {
        if !self.forward_subst.contains_key(&lit_id.abs()) {
            // TODO: finish it
            while (lit_id.abs() as usize) > self.solver.n_vars() {
                let idx = (self.solver.n_vars() + 1) as i32;
                self.new_var(idx);
            }
        }

        self.forward_subst[&lit_id.abs()].sign_lit(lit_id < 0)
    }

    fn new_var(&mut self, var_id: i32) {
        let v = self.solver.new_var(None, true);
        self.forward_subst.insert(var_id, v);
        self.backward_subst.insert(&v, var_id);
    }
}


struct DimacsParser<'p> {
    reader: str::Chars<'p>,
    cur: Option<char>,
    vars: HashSet<i32>,
    clauses: usize,
}

impl<'p> DimacsParser<'p> {
    pub fn parse<R: io::Read + 'p, F: FnMut(Vec<i32>) -> ()>(
        mut reader: R,
        validate: bool,
        clause: F,
    ) -> io::Result<()> {
        let mut buf = String::new();
        reader.read_to_string(&mut buf)?;

        let mut p = DimacsParser {
            reader: buf.chars(),
            cur: None,
            vars: HashSet::new(),
            clauses: 0,
        };
        p.next()?;
        p.parse_me(validate, clause)
    }

    fn parse_me<F: FnMut(Vec<i32>) -> ()>(
        &mut self,
        validate: bool,
        mut clause: F,
    ) -> io::Result<()> {
        enum State {
            Waiting,
            Parsing(usize, usize),
        }

        let mut state = State::Waiting;
        loop {
            self.skip_whitespace()?;
            match state {
                State::Waiting => match self.current() {
                    Some('c') => {
                        self.skip_line()?;
                    }

                    _ => {
                        self.consume("p cnf")?;
                        let vars = self.next_uint()?;
                        let clauses = self.next_uint()?;
                        state = State::Parsing(vars, clauses);
                    }
                },

                State::Parsing(vars, clauses) => match self.current() {
                    Some('c') => {
                        self.skip_line()?;
                    }

                    None => {
                        if validate {
                            if clauses != self.clauses {
                                return Err(io::Error::new(io::ErrorKind::Other,
                                        format!("PARSE ERROR! DIMACS header mismatch: {} clauses declared, {} found", clauses, self.clauses)));
                            }

                            if vars < self.vars.len() {
                                return Err(io::Error::new(io::ErrorKind::Other,
                                        format!("PARSE ERROR! DIMACS header mismatch: {} vars declared, {} discovered", vars, self.vars.len())));
                            }
                        }
                        return Ok(());
                    }

                    _ => {
                        let c = self.parse_clause()?;
                        clause(c);
                    }
                },
            }
        }
    }

    fn parse_clause(&mut self) -> io::Result<Vec<i32>> {
        let mut lits = Vec::new();
        loop {
            let lit = self.next_int()?;
            if lit == 0 {
                self.clauses += 1;
                return Ok(lits);
            } else {
                self.vars.insert(lit.abs());
                lits.push(lit);
            }
        }
    }


    #[inline]
    pub fn next(&mut self) -> io::Result<()> {
        self.cur = self.reader.next();
        Ok(())
    }

    #[inline]
    pub fn current(&self) -> Option<char> {
        self.cur
    }

    pub fn skip_whitespace(&mut self) -> io::Result<()> {
        loop {
            match self.cur {
                None => break,
                Some(c) if !c.is_whitespace() => break,
                _ => self.next()?,
            }
        }
        Ok(())
    }

    pub fn skip_line(&mut self) -> io::Result<()> {
        loop {
            match self.cur {
                None => break,
                Some('\n') => {
                    self.next()?;
                    break;
                }
                _ => self.next()?,
            }
        }
        Ok(())
    }

    pub fn consume(&mut self, target: &str) -> io::Result<()> {
        for tc in target.chars() {
            match self.cur {
                Some(c) if c == tc => self.next()?,
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        format!("failed to consume; expected '{}'", target),
                    ));
                }
            }
        }
        Ok(())
    }

    fn read_int_body(&mut self) -> io::Result<usize> {
        let mut len: usize = 0;
        let mut value = 0;
        loop {
            match self.cur.and_then(|c| c.to_digit(10)) {
                Some(d) => {
                    value = value * 10 + (d as usize);
                    len += 1;
                    self.next()?
                }

                _ if len > 0 => return Ok(value),

                _ => {
                    return Err(io::Error::new(io::ErrorKind::Other, "int expected"));
                }
            }
        }
    }

    pub fn next_int(&mut self) -> io::Result<i32> {
        self.skip_whitespace()?;
        let sign = match self.cur {
            Some('+') => {
                self.next()?;
                1
            }
            Some('-') => {
                self.next()?;
                -1
            }
            _ => 1,
        };

        let val = self.read_int_body()?;
        Ok(sign * (val as i32))
    }

    pub fn next_uint(&mut self) -> io::Result<usize> {
        self.skip_whitespace()?;
        match self.cur {
            Some('+') => self.next()?,
            _ => {}
        }
        self.read_int_body()
    }
}
