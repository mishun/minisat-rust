use std::io;
use super::index_map::{HasIndex};
use super::literal::{Var, Lit};
use super::lbool::{LBool};
use super::solver::{Solver};


fn parse_clause<R : io::Read>(p : &mut BufferParser<R>) -> io::Result<Vec<Lit>> {
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

pub fn parse_DIMACS<R : io::Read, S : Solver>(chars : io::Chars<R>, solver : &mut S, validate : bool) -> io::Result<()> {
    let mut p = try!(BufferParser::new(chars));

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
                                solver.newVar(LBool::Undef(), true);
                            }
                        }
                        solver.addClause(c.as_slice());
                    }
                }
            }
        }
    }
}



pub struct BufferParser<R> {
    reader : io::Chars<R>,
    cur    : Option<char>,
}

impl<R : io::Read> BufferParser<R> {
    pub fn new(r : io::Chars<R>) -> io::Result<BufferParser<R>> {
        let mut p : BufferParser<R> = BufferParser { reader : r, cur : None };
        try!(p.next());
        Ok(p)
    }

    #[inline]
    pub fn next(&mut self) -> io::Result<()> {
        match self.reader.next() {
            Some(Ok(c))    => { self.cur = Some(c); Ok(()) }
            None           => { self.cur = None; Ok(()) }
            Some(Err(err)) => { self.cur = None; Err(io::Error::new(io::ErrorKind::Other, err)) }
        }
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
