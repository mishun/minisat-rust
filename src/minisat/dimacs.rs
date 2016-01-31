// TODO: wait for io stabilization and completely rewrite it
use std::io;
use std::str;
use std::borrow::Borrow;
use std::collections::HashMap;
use super::index_map::IndexMap;
use super::literal::{Var, Lit};
use super::solver::Solver;


pub fn write<W : io::Write, S : Solver>(_ : &mut W, _ : &S) -> io::Result<()> {
    // TODO: implement
    unimplemented!()
}


pub fn parse<R : io::Read, S : Solver>(reader : &mut R, solver : &mut S, validate : bool) -> io::Result<IndexMap<Var, i32>> {
    let mut buf = String::new();
    try!(reader.read_to_string(&mut buf));

    let mut parser =
        DimacsParser {
            forward_subst  : HashMap::new(),
            backward_subst : IndexMap::new(),
            parser         : try!(Parser::new(buf.chars())),
            solver         : solver
        };

    try!(parser.parse(validate));
    Ok(parser.backward_subst)
}


struct DimacsParser<'p, 's, S : 's> {
    forward_subst  : HashMap<i32, Var>,
    backward_subst : IndexMap<Var, i32>,
    parser         : Parser<'p>,
    solver         : &'s mut S
}

impl<'p, 's, S : Solver> DimacsParser<'p, 's, S> {
    fn parse(&mut self, validate : bool) -> io::Result<()> {
        enum State { Waiting, Parsing(usize, usize) }

        let mut state = State::Waiting;
        loop {
            try!(self.parser.skipWhitespace());
            match state {
                State::Waiting => {
                    match self.parser.current() {
                        Some('c') => { try!(self.parser.skipLine()); }

                        _         => {
                            try!(self.parser.consume("p cnf"));
                            let vars = try!(self.parser.nextUInt());
                            let clauses = try!(self.parser.nextUInt());
                            state = State::Parsing(vars, clauses);
                        }
                    }
                }

                State::Parsing(vars, clauses) => {
                    match self.parser.current() {
                        Some('c') => { try!(self.parser.skipLine()); }

                        None      => {
                            if validate && (clauses != self.solver.nClauses() || vars < self.solver.nVars()) {
                                return Err(io::Error::new(io::ErrorKind::Other, "PARSE ERROR! DIMACS header mismatch"));
                            }
                            return Ok(());
                        }

                        _         => {
                            let c = try!(self.parseClause());
                            self.solver.addClause(c.borrow());
                        }
                    }
                }
            }
        }
    }

    fn parseClause(&mut self) -> io::Result<Vec<Lit>> {
        let mut lits = Vec::new();
        loop {
            let lit = try!(self.parser.nextInt());
            if lit == 0 {
                return Ok(lits);
            } else {
                lits.push(Lit::new(self.varById(lit.abs()), lit < 0));
            }
        }
    }

    fn varById(&mut self, var_id : i32) -> Var {
        if !self.forward_subst.contains_key(&var_id) {
            // TODO: finish it
            //self.newVar(var_id);
            while (var_id as usize) > self.solver.nVars() {
                let idx = (self.solver.nVars() + 1) as i32;
                self.newVar(idx);
            }
        }

        self.forward_subst[&var_id]
    }

    fn newVar(&mut self, var_id : i32) {
        let v = self.solver.newVar(None, true);
        self.forward_subst.insert(var_id, v);
        self.backward_subst.insert(&v, var_id);
    }
}


struct Parser<'a> {
    reader : str::Chars<'a>,
    cur    : Option<char>
}

impl<'a> Parser<'a> {
    pub fn new(r : str::Chars<'a>) -> io::Result<Parser<'a>> {
        let mut p : Parser<'a> = Parser { reader : r, cur : None };
        try!(p.next());
        Ok(p)
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
