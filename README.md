Functional Pearl: Getting a Quick Fix on Comonads
-------------------------------------------------

K. Foner. "Functional  Pearl: Getting  a  Quick  Fix on Comonads." In *Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell.*  ACM, 2015.

This repository contains the full source material for the above paper, in the form of literate Haskell which can either be compiled to a PDF of the paper, or to executable code for the library it describes.

The quickest way to read the paper is to [download the compiled pre-print PDF](https://github.com/kwf/GQFC/raw/master/GQFC.pdf).

## Abstract

A piece of functional programming folklore due to Piponi provides Löb's theorem from modal provability logic with a computational interpretation as an unusual fixed point. Interpreting modal necessity as an arbitrary `Functor` in Haskell, the "type" of Löb's theorem is inhabited by a fixed point function allowing each part of a structure to refer to the whole.

However, `Functor`'s logical interpretation may be used to prove Löb's theorem only by relying on its implicit functorial strength, an axiom not available in the provability modality. As a result, the well known loeb fixed point "cheats" by using functorial strength to implement its recursion.

Rather than `Functor`, a closer Curry analogue to modal logic's Howard inspiration is a closed (semi-)comonad, of which Haskell's `ComonadApply` typeclass provides analogous structure. Its computational interpretation permits the definition of a novel fixed point function allowing each part of a structure to refer to its own context within the whole. This construction further guarantees maximal sharing and asymptotic efficiency superior to loeb for locally contextual computations upon a large class of structures. With the addition of a distributive law, closed comonads may be composed into spaces of arbitrary dimensionality while preserving the performance guarantees of this new fixed point.

From these elements, we construct a small embedded domain-specific language to elegantly express and evaluate multidimensional "spreadsheet-like" recurrences for a variety of cellular automata.

## Playing Along with the Code

**Requirements:**
- a working installation of `GHC` version 7.8 or higher
- a relatively recent version of `cabal` (supporting sandboxes)

**What to do:**
Build the paper's code by running `./build-code`, then enter a REPL by running `cabal repl`.

## Building the Paper

**Requirements:**
- a working `LaTeX` installation
- the program [`latexmk`](https://www.ctan.org/pkg/latexmk/?lang=en) (which may have come with your `LaTeX` distribution)
- the program [`lhs2TeX`](http://www.andres-loeh.de/lhs2tex) (to get it, just `cabal install lhs2tex`)

**What to do:**
Running `./build-paper`, which will generate the PDF at `./GQFC.pdf`.

## Reading Only the Code

In some circumstances, it might be desirable to read only the source code for the paper, without any of the text.

**Requirements**
- the program [`unlit`](https://hackage.haskell.org/package/unlit) (to get it, just `cabal install unlit`)

**What to do:**
Run `./extract-code`, which will generate a file `./GQFC.hs` containing only the code for the library.

After that, you can open this file in your favorite editor to read the paper as `GHC` sees it.
