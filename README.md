TurtleRegex
===========

Toy regex engine in haskell.    
Support `|`, `*`, `+`, `?`, `.`, `\d`, `\s`, `(...)`, `{x,y}`, `[a-z]`, `[^...]`.

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
λ> let p = compile "http://[a-zA-Z0-9\\-\\.]+\\.[a-zA-Z]{2,3}(/[^\\s]*)?"
λ> match p "http://www.twitter.com/scturtle"
Right "http://www.twitter.com/scturtle"
λ> match p "https://www.twitter.com/"
Left "http"
```
