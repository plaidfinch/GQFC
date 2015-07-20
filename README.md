## Building the Paper

You need a working `LaTeX` installation, as well as the programs `lhs2TeX` and `latexmk`. Once you have these installed:

```
lhs2TeX GQFC.lhs -o GQFC.tex; latexmk -pdf GQFC
```

## Playing Along with the Code

```
cabal sandbox init
cabal install --only-dependencies
cabal configure
cabal repl
```
