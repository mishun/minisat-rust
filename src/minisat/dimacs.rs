// TODO: wait for io stabilization and completely rewrite it
use std::io;
use std::str;
use std::borrow::Borrow;
use super::index_map::HasIndex;
use super::literal::{Var, Lit};
use super::solver::Solver;


pub fn parse<R : io::Read, S : Solver>(reader : &mut R, solver : &mut S, validate : bool) -> io::Result<()> {
    let mut buf = String::new();
    let _ = try!(reader.read_to_string(&mut buf));
    let mut p = try!(Parser::new(buf.chars()));

    enum State { Waiting, Parsing(usize, usize) }

    let mut state = State::Waiting;
    loop {
        try!(p.skipWhitespace());
        match state {
            State::Waiting => {
                match p.current() {
                    Some('c') => { try!(p.skipLine()); }
                    _         => {
                        try!(p.consume("p cnf"));
                        let vars = try!(p.nextUInt());
                        let clauses = try!(p.nextUInt());
                        state = State::Parsing(vars, clauses);
                    }
                }
            }

            State::Parsing(vars, clauses) => {
                match p.current() {
                    Some('c') => { try!(p.skipLine()); }

                    None      => {
                        if validate && (clauses != solver.nClauses() || vars < solver.nVars()) {
                            return Err(io::Error::new(io::ErrorKind::Other, "PARSE ERROR! DIMACS header mismatch"));
                        }
                        return Ok(());
                    }

                    _         => {
                        let c = try!(parse_clause(&mut p));
                        for l in c.iter() {
                            while l.var().toIndex() >= solver.nVars() {
                                solver.newVar(None, true);
                            }
                        }
                        solver.addClause(c.borrow());
                    }
                }
            }
        }
    }
}

fn parse_clause<'a>(p : &mut Parser<'a>) -> io::Result<Vec<Lit>> {
    let mut lits : Vec<Lit> = Vec::new();
    loop {
        let lit = try!(p.nextInt());
        if lit == 0 {
            return Ok(lits);
        } else {
            let var = (lit.abs() as usize) - 1;
            lits.push(Lit::new(Var::new(var), lit < 0));
        }
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
