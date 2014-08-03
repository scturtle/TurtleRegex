TurtleRegex
===========

Toy regex engine in haskell.    
Support `|`, `*`, `+`, `?`, `.`, `\d`, `\s`, `(...)`, `{x,y}`.

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
