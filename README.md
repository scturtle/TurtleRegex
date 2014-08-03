TurtleRegex
===========

Toy Regex Engine in Haskell

#### Usage

Build module:
```
$ cabal build
```

Test in REPL:
```
$ cabal repl
......
Ok, modules loaded: TurtleRegex.
λ> let p = compile "a?b{3,5}c"
λ> match p "abbc"
Left "abb"
λ> match p "abbbbc"
Right "abbbbc"
```
