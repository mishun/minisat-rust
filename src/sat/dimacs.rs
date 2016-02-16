// TODO: wait for io stabilization and completely rewrite it
use std::{fs, io, path, str};
use std::collections::{HashSet, HashMap};
use flate2::read::GzDecoder;
use sat::formula::{Var, Lit, VarMap};
use sat::Solver;


pub fn write<W : io::Write, S : Solver>(_ : &mut W, _ : &S) -> io::Result<()> {
    // TODO: implement
    unimplemented!()
}


pub fn parseFile<P : AsRef<path::Path>, S : Solver>(path : &P, solver : &mut S, validate : bool) -> io::Result<VarMap<i32>> {
    let open = || { fs::File::open(path).map(|file| io::BufReader::new(file)) };
    match GzDecoder::new(try!(open())) {
        Ok(mut gz) => { parse(&mut gz, solver, validate) }
        Err(_)     => { parse(&mut try!(open()), solver, validate) }
    }
}


pub fn parse<R : io::Read, S : Solver>(stream : &mut R, solver : &mut S, validate : bool) -> io::Result<VarMap<i32>> {
    let mut subst = Subst::new(solver);
    try!(DimacsParser::parse(stream, validate, |cl| { subst.addClause(cl) }));
    Ok(subst.backward_subst)
}


pub fn writeModel<W : io::Write>(stream : &mut W, backward_subst : &VarMap<i32>, model : &VarMap<bool>) -> io::Result<()> {
    for (var, &val) in model.iter() {
        let var_id = backward_subst[&var];
        try!(write!(stream, "{} ", if val { var_id } else { -var_id }));
    }
    try!(writeln!(stream, "0"));
    Ok(())
}


pub fn validateModelFile<P : AsRef<path::Path>>(path : &P, backward_subst : &VarMap<i32>, model : &VarMap<bool>) -> io::Result<bool> {
    let open = || { fs::File::open(path).map(|file| io::BufReader::new(file)) };
    match GzDecoder::new(try!(open())) {
        Ok(mut gz) => { validateModel(&mut gz, backward_subst, model) }
        Err(_)     => { validateModel(&mut try!(open()), backward_subst, model) }
    }
}

pub fn validateModel<R : io::Read>(stream : &mut R, backward_subst : &VarMap<i32>, model : &VarMap<bool>) -> io::Result<bool> {
    let mut lits = HashSet::new();
    for (var, &value) in model.iter() {
        let lit_id = {
            let var_id = backward_subst[&var];
            if value { var_id } else { -var_id }
        };

        lits.insert(lit_id);
        if lits.contains(&(-lit_id)) {
            return Ok((false));
        }
    }

    let mut ok = true;
    try!(DimacsParser::parse(stream, false, |cl| {
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
    }));

    Ok(ok)
}


struct Subst<'s, S : 's> {
    solver         : &'s mut S,
    forward_subst  : HashMap<i32, Var>,
    backward_subst : VarMap<i32>
}

impl<'s, S : Solver> Subst<'s, S> {
    pub fn new(solver : &'s mut S) -> Self {
        Subst { solver         : solver
              , forward_subst  : HashMap::new()
              , backward_subst : VarMap::new()
              }
    }

    pub fn addClause(&mut self, raw : Vec<i32>) {
        let lits : Vec<Lit> = raw.iter().map(|&lit_id| { self.litById(lit_id) }).collect();
        self.solver.addClause(&lits[..]);
    }

    fn litById(&mut self, lit_id : i32) -> Lit {
        if !self.forward_subst.contains_key(&lit_id.abs()) {
            // TODO: finish it
            while (lit_id.abs() as usize) > self.solver.nVars() {
                let idx = (self.solver.nVars() + 1) as i32;
                self.newVar(idx);
            }
        }

        self.forward_subst[&lit_id.abs()].lit(lit_id < 0)
    }

    fn newVar(&mut self, var_id : i32) {
        let v = self.solver.newVar(None, true);
        self.forward_subst.insert(var_id, v);
        self.backward_subst.insert(&v, var_id);
    }
}


struct DimacsParser<'p> {
    reader  : str::Chars<'p>,
    cur     : Option<char>,
    vars    : HashSet<i32>,
    clauses : usize
}

impl<'p> DimacsParser<'p> {
    pub fn parse<R : io::Read, F : FnMut(Vec<i32>) -> ()>(reader : &'p mut R, validate : bool, clause : F) -> io::Result<()> {
        let mut buf = String::new();
        try!(reader.read_to_string(&mut buf));

        let mut p = DimacsParser { reader  : buf.chars()
                                 , cur     : None
                                 , vars    : HashSet::new()
                                 , clauses : 0
                                 };
        try!(p.next());
        p.parseMe(validate, clause)
    }

    fn parseMe<F : FnMut(Vec<i32>) -> ()>(&mut self, validate : bool, mut clause : F) -> io::Result<()> {
        enum State { Waiting, Parsing(usize, usize) }

        let mut state = State::Waiting;
        loop {
            try!(self.skipWhitespace());
            match state {
                State::Waiting => {
                    match self.current() {
                        Some('c') => { try!(self.skipLine()); }

                        _         => {
                            try!(self.consume("p cnf"));
                            let vars = try!(self.nextUInt());
                            let clauses = try!(self.nextUInt());
                            state = State::Parsing(vars, clauses);
                        }
                    }
                }

                State::Parsing(vars, clauses) => {
                    match self.current() {
                        Some('c') => { try!(self.skipLine()); }

                        None      => {
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

                        _         => {
                            let c = try!(self.parseClause());
                            clause(c);
                        }
                    }
                }
            }
        }
    }

    fn parseClause(&mut self) -> io::Result<Vec<i32>> {
        let mut lits = Vec::new();
        loop {
            let lit = try!(self.nextInt());
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
                None                          => break,
                Some(c) if !c.is_whitespace() => break,
                _                             => try!(self.next())
            }
        }
        Ok(())
    }

    pub fn skipLine(&mut self) -> io::Result<()> {
        loop {
            match self.cur {
                None       => break,
                Some('\n') => { try!(self.next()); break; }
                _          => { try!(self.next()) }
            }
        }
        Ok(())
    }

    pub fn consume(&mut self, target : &str) -> io::Result<()> {
        for tc in target.chars() {
            match self.cur {
                Some(c) if c == tc => { try!(self.next()) }
                _                  => {
                    return Err(io::Error::new(io::ErrorKind::Other, format!("failed to consume; expected '{}'", target)));
                }
            }
        }
        Ok(())
    }

    fn readIntBody(&mut self) -> io::Result<usize> {
        let mut len : usize = 0;
        let mut value = 0;
        loop {
            match self.cur.and_then(|c| { c.to_digit(10) }) {
                Some(d)      => {
                    value = value * 10 + (d as usize);
                    len += 1;
                    try!(self.next())
                }

                _ if len > 0 => { return Ok(value) }

                _            => {
                    return Err(io::Error::new(io::ErrorKind::Other, "int expected"));
                }
            }
        }
    }

    pub fn nextInt(&mut self) -> io::Result<i32> {
        try!(self.skipWhitespace());
        let sign =
            match self.cur {
                Some('+') => { try!(self.next()); 1 }
                Some('-') => { try!(self.next()); -1 }
                _         => 1
            };

        let val = try!(self.readIntBody());
        Ok(sign * (val as i32))
    }

    pub fn nextUInt(&mut self) -> io::Result<usize> {
        try!(self.skipWhitespace());
        match self.cur {
            Some('+') => { try!(self.next()) }
            _         => {}
        }
        self.readIntBody()
    }
}
