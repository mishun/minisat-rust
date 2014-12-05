use std::num::{SignedInt};
use std::io;
use super::literal::{Var, Lit};
use super::lbool::{LBool};
use super::core_solver::{Solver};
use super::index_map::{HasIndex};


fn parse_clause<B : Buffer>(p : &mut BufferParser<B>) -> io::IoResult<Vec<Lit>> {
    let mut lits : Vec<Lit> = Vec::new();
    loop {
        let lit = try!(p.nextInt());
        if lit == 0 {
            return Ok(lits);
        } else {
            let var = lit.abs() as uint - 1;
            lits.push(Lit::new(Var::new(var), lit < 0));
        }
    }
}

pub fn parse_DIMACS<B : io::Buffer, S : Solver>(buffer : &mut B, solver : &mut S, validate : bool) -> io::IoResult<()> {
    let mut p = try!(BufferParser::new(buffer));

    enum State { Waiting, Parsing(uint, uint) }

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
                            return Err(
                                io::IoError {
                                    kind   : io::OtherIoError,
                                    desc   : "PARSE ERROR! DIMACS header mismatch",
                                    detail : None
                                });
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



pub struct BufferParser<'r, R : 'r> {
    reader : &'r mut R,
    cur : Option<char>,
}

impl<'r, R : Buffer> BufferParser<'r, R> {
    pub fn new(r : &'r mut R) -> io::IoResult<BufferParser<'r, R>> {
        let mut p : BufferParser<R> = BufferParser { reader : r, cur : None };
        try!(p.next());
        Ok(p)
    }

    #[inline]
    pub fn next(&mut self) -> io::IoResult<()> {
        match self.reader.read_char() {
            Ok(c)                                         => { self.cur = Some(c); Ok(()) }
            Err(io::IoError { kind : io::EndOfFile, .. }) => { self.cur = None; Ok(()) }
            Err(err)                                      => { Err(err) }
        }
    }

    #[inline]
    pub fn current(&self) -> Option<char> {
        self.cur
    }

    pub fn skipWhitespace(&mut self) -> io::IoResult<()> {
        loop {
            match self.cur {
                None                          => break,
                Some(c) if !c.is_whitespace() => break,
                _                             => try!(self.next())
            }
        }
        Ok(())
    }

    pub fn skipLine(&mut self) -> io::IoResult<()> {
        loop {
            match self.cur {
                None       => break,
                Some('\n') => { try!(self.next()); break; }
                _          => { try!(self.next()) }
            }
        }
        Ok(())
    }

    pub fn consume(&mut self, target : &str) -> io::IoResult<()> {
        for tc in target.chars() {
            match self.cur {
                Some(c) if c == tc => { try!(self.next()) }
                _                  => {
                    return Err(
                        io::IoError {
                            kind   : io::OtherIoError,
                            desc   : "failed to consume",
                            detail : Some(format!("expected '{}'", target))
                        });
                }
            }
        }
        Ok(())
    }

    fn readIntBody(&mut self) -> io::IoResult<uint> {
        let mut len : uint = 0;
        let mut value = 0;
        loop {
            match self.cur.and_then(|c| { c.to_digit(10) }) {
                Some(d)      => {
                    value = value * 10 + d;
                    len += 1;
                    try!(self.next())
                }

                _ if len > 0 => { return Ok(value) }

                _            => {
                    return Err(
                        io::IoError {
                            kind   : io::OtherIoError,
                            desc   : "int expected",
                            detail : None
                        });
                }
            }
        }
    }

    pub fn nextInt(&mut self) -> io::IoResult<int> {
        try!(self.skipWhitespace());
        let sign =
            match self.cur {
                Some('+') => { try!(self.next()); 1 }
                Some('-') => { try!(self.next()); -1 }
                _         => 1
            };

        let val = try!(self.readIntBody());
        Ok(sign * val as int)
    }

    pub fn nextUInt(&mut self) -> io::IoResult<uint> {
        try!(self.skipWhitespace());
        match self.cur {
            Some('+') => { try!(self.next()) }
            _         => {}
        }
        self.readIntBody()
    }
}
