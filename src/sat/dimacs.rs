// TODO: wait for io stabilization and completely rewrite it
use std::{fs, io, path, str};
use std::io::{Seek, SeekFrom};
use std::collections::{HashMap, HashSet};
use flate2::read::GzDecoder;
use sat::formula::{Lit, Var, VarMap};
use sat::{SolveRes, Solver};


pub fn write<W: io::Write, S: Solver>(_: W, _: &S) -> io::Result<()> {
    // TODO: implement
    unimplemented!()
}


pub fn parseFile<P: AsRef<path::Path>, S: Solver>(
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
    DimacsParser::parse(reader, validate, |cl| subst.addClause(cl))?;
    Ok(subst.backward_subst)
}


pub fn writeResult<W: io::Write, S>(
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


pub fn validateModelFile<P: AsRef<path::Path>>(
    path: P,
    backward_subst: &VarMap<i32>,
    model: &Vec<Lit>,
) -> io::Result<bool> {
    let mut reader = io::BufReader::new(fs::File::open(path)?);
    {
        let gz = GzDecoder::new(&mut reader);
        if gz.header().is_some() {
            return validateModel(gz, backward_subst, model);
        }
    }

    reader.seek(SeekFrom::Start(0))?;
    validateModel(reader, backward_subst, model)
}

pub fn validateModel<R: io::Read>(
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
            return Ok((false));
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
            solver: solver,
            forward_subst: HashMap::new(),
            backward_subst: VarMap::new(),
        }
    }

    pub fn addClause(&mut self, raw: Vec<i32>) {
        let lits: Vec<Lit> = raw.iter().map(|&lit_id| self.litById(lit_id)).collect();
        self.solver.addClause(&lits[..]);
    }

    fn litById(&mut self, lit_id: i32) -> Lit {
        if !self.forward_subst.contains_key(&lit_id.abs()) {
            // TODO: finish it
            while (lit_id.abs() as usize) > self.solver.nVars() {
                let idx = (self.solver.nVars() + 1) as i32;
                self.newVar(idx);
            }
        }

        self.forward_subst[&lit_id.abs()].lit(lit_id < 0)
    }

    fn newVar(&mut self, var_id: i32) {
        let v = self.solver.newVar(None, true);
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
        p.parseMe(validate, clause)
    }

    fn parseMe<F: FnMut(Vec<i32>) -> ()>(
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
            self.skipWhitespace()?;
            match state {
                State::Waiting => match self.current() {
                    Some('c') => {
                        self.skipLine()?;
                    }

                    _ => {
                        self.consume("p cnf")?;
                        let vars = self.nextUInt()?;
                        let clauses = self.nextUInt()?;
                        state = State::Parsing(vars, clauses);
                    }
                },

                State::Parsing(vars, clauses) => match self.current() {
                    Some('c') => {
                        self.skipLine()?;
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
                        let c = self.parseClause()?;
                        clause(c);
                    }
                },
            }
        }
    }

    fn parseClause(&mut self) -> io::Result<Vec<i32>> {
        let mut lits = Vec::new();
        loop {
            let lit = self.nextInt()?;
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

    pub fn skipWhitespace(&mut self) -> io::Result<()> {
        loop {
            match self.cur {
                None => break,
                Some(c) if !c.is_whitespace() => break,
                _ => self.next()?,
            }
        }
        Ok(())
    }

    pub fn skipLine(&mut self) -> io::Result<()> {
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

    fn readIntBody(&mut self) -> io::Result<usize> {
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

    pub fn nextInt(&mut self) -> io::Result<i32> {
        self.skipWhitespace()?;
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

        let val = self.readIntBody()?;
        Ok(sign * (val as i32))
    }

    pub fn nextUInt(&mut self) -> io::Result<usize> {
        self.skipWhitespace()?;
        match self.cur {
            Some('+') => self.next()?,
            _ => {}
        }
        self.readIntBody()
    }
}
