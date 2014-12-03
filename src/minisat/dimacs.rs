use std::num::{SignedInt};
use std::io::{Buffer};
use super::literal::{Var, Lit};
use super::lbool::{LBool};
use super::core_solver::{Solver};
use super::index_map::{HasIndex};


fn parse_clause<B : Buffer>(p : &mut BufferParser<B>) -> Option<Vec<Lit>> {
    let mut lits : Vec<Lit> = Vec::new();
    loop {
        let tmp = p.nextInt();
        match tmp {
            None      => { return None; }
            Some(0)   => { return Some(lits); }
            Some(lit) => {
                let var = lit.abs() as uint - 1;
                lits.push(Lit::new(Var::new(var), lit < 0));
            }
        }
    }
}

pub fn parse_DIMACS<B : Buffer, S : Solver>(buffer : &mut B, solver : &mut S, validate : bool) -> bool {
    let mut p = BufferParser::new(buffer);

    enum State { Waiting, Parsing(uint, uint) }

    let mut state = State::Waiting;
    loop {
        p.skipWhitespace();
        match state {
            State::Waiting => {
                match p.current() {
                    Some('c')      => { p.skipLine(); }
                    Some('p')      => {
                        if !p.consume("p cnf") { return false; }
                        let vars = p.nextUInt();
                        let clauses = p.nextUInt();
                        if vars.is_none() || clauses.is_none() { return false; }
                        state = State::Parsing(vars.unwrap(), clauses.unwrap());
                    }
                    None | Some(_) => { return false; }
                }
            }

            State::Parsing(vars, clauses) => {
                match p.current() {
                    Some('c') => { p.skipLine(); }

                    None      => {
                        if validate && (clauses != solver.nClauses() || vars < solver.nVars()) {
                            println!("PARSE ERROR! DIMACS header mismatch");
                            return false;
                        }
                        return true;
                    }

                    _         => {
                        match parse_clause(&mut p) {
                            None    => { return false; }
                            Some(c) => {
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
    }
}



pub struct BufferParser<'r, R : 'r> {
    reader : &'r mut R,
    cur : Option<char>,
}

impl<'r, R : Buffer> BufferParser<'r, R> {
    pub fn new(r : &'r mut R) -> BufferParser<'r, R> {
        let mut p : BufferParser<R> = BufferParser { reader : r, cur : None };
        p.next();
        p
    }

    pub fn next(&mut self) {
        self.cur = self.reader.read_char().ok()
    }

    pub fn current(&self) -> Option<char> {
        self.cur
    }

    pub fn skipWhitespace(&mut self) {
        loop {
            match self.cur {
                None                          => break,
                Some(c) if !c.is_whitespace() => break,
                _                             => self.next()
            }
        }
    }

    pub fn skipLine(&mut self) {
        loop {
            match self.cur {
                None       => break,
                Some('\n') => { self.next(); break; }
                _          => self.next()
            }
        }
    }

    pub fn consume(&mut self, target : &str) -> bool {
        for tc in target.chars() {
            match self.cur {
                Some(c) if c == tc => { self.next() }
                _                  => { return false }
            }
        }
        true
    }


    fn readIntBody(&mut self) -> Option<uint> {
        let mut len : uint = 0;
        let mut value = 0;
        loop {
            match self.cur.and_then(|c| { c.to_digit(10) }) {
                Some(d)      => {
                    value = value * 10 + d;
                    len += 1;
                    self.next();
                }
                _ if len > 0 => return Some(value),
                _            => return None
            }
        }
    }

    pub fn nextInt(&mut self) -> Option<int> {
        self.skipWhitespace();
        let sign =
            match self.cur {
                Some('+') => { self.next(); 1 }
                Some('-') => { self.next(); -1 }
                _         => 1
            };

        self.readIntBody().map(|val| { sign * val as int })
    }

    pub fn nextUInt(&mut self) -> Option<uint> {
        self.skipWhitespace();
        match self.cur {
            Some('+') => { self.next() }
            _         => {}
        }
        self.readIntBody()
    }
}

