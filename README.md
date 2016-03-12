# minisat-rust

[![Build Status](https://travis-ci.org/mishun/minisat-rust.svg?branch=master)](https://travis-ci.org/mishun/minisat-rust)

Note that this is reimplementation, not bindings.

Original minisat links:
  - https://github.com/niklasso/minisat
  - http://minisat.se/

## Using

Pretty much identical to original minisat. The only difference is using pair of dashes
before each argument instead of just one.
So, instead of something like:
```sh
$ minisat -verb=2 -rsync input.cnf
```
we have:
```sh
$ minisat-rust --verb=2 --rsync input.cnf
```

This is because I am too lazy to reimplement minisat's custom argument parsing and used
existing library instead :)

## Building

Just use Cargo. You should have minisat in your path if you want to run big test
that solves bunch of cnf files and compares output to minisat.

## What is not working yet?

  - Reading (gzipped) CNF from stdin.
  - Proper allocation/reallocation of clauses (GC log messages are fake to test output
    against minisat). Probably need to wait Rust allocation features stabilization
    before implementing it.
  - Proper Ctrl-C handling.
  - Writing DIMACS when solving is interrupted.

## Why?

There are a few reasons for reimplementing instead of just writing bindings:
  - Evaluate how Rust is suitable for relatively big projects
  - Estimate performance degradation (~1.5 -- 2 times for now; maybe I am just bad at Rust).
  - Minisat code is quite complicated having big structure randomly mutated by bunch of
    methods. Rust encourages splitting it into smaller more tractable parts that could
    help understanding how minisat actually works and verify it with Rust type system.
  - Maybe find some minisat bugs as a result of previous point.
    Indeed at least one was found: [Issue 26](https://github.com/niklasso/minisat/issues/26).
