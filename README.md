Functional Pearl: Getting a Quick Fix on Comonads
-------------------------------------------------

K. Foner. "Functional  Pearl: Getting  a  Quick  Fix on Comonads." In *Proceedings of the 2015 ACM SIGPLAN Symposium on Haskell.*  ACM, 2015.

This repository contains the full source material for the above paper, in the form of literate Haskell which can either be compiled to a PDF of the paper, or to executable code for the library it describes.

The quickest way to read the paper is to [download the compiled pre-print PDF](https://github.com/kwf/GQFC/raw/master/GQFC.pdf).

![The lfix function described in the paper](lfix.png)

## Abstract

A piece of functional programming folklore due to Piponi provides Löb's theorem from modal provability logic with a computational interpretation as an unusual fixed point. Interpreting modal necessity as an arbitrary `Functor` in Haskell, the "type" of Löb's theorem is inhabited by a fixed point function allowing each part of a structure to refer to the whole.

However, `Functor`'s logical interpretation may be used to prove Löb's theorem only by relying on its implicit functorial strength, an axiom not available in the provability modality. As a result, the well known loeb fixed point "cheats" by using functorial strength to implement its recursion.

Rather than `Functor`, a closer Curry analogue to modal logic's Howard inspiration is a closed (semi-)comonad, of which Haskell's `ComonadApply` typeclass provides analogous structure. Its computational interpretation permits the definition of a novel fixed point function allowing each part of a structure to refer to its own context within the whole. This construction further guarantees maximal sharing and asymptotic efficiency superior to loeb for locally contextual computations upon a large class of structures. With the addition of a distributive law, closed comonads may be composed into spaces of arbitrary dimensionality while preserving the performance guarantees of this new fixed point.

From these elements, we construct a small embedded domain-specific language to elegantly express and evaluate multidimensional "spreadsheet-like" recurrences for a variety of cellular automata.

## Quick Start

To build all the artifacts in the project, you need:

- A version of `GHC` 7.8 or greater
- A version of `cabal` supporting sandboxes (i.e. 1.18 or greater)
- A working `LaTeX` installation
- [`latexmk`](https://www.ctan.org/pkg/latexmk/?lang=en) (which may have come with your `LaTeX` distribution)
- [`lhs2TeX`](http://www.andres-loeh.de/lhs2tex) (to get it:  `cabal install lhs2tex`)
- [`unlit`](https://hackage.haskell.org/package/unlit) (to get it: `cabal install unlit`)

The script `./build-everything` creates a `cabal` sandbox and builds all the artifacts.

After that, you can...

- view `./GQFC.pdf` to read the paper
- run `cabal repl` to launch a REPL with the code
- view `./GQFC.hs` to read *only* the code with the paper text elided

Below are details about building each of the artifacts individually.

### Playing Along with the Code

Run `./build-code` once to build things, then enter a REPL by running `cabal repl`.

### Building the Paper

Run `./build-paper`, which will generate the paper's PDF at `./GQFC.pdf`.

### Reading Only the Code

Run `./extract-code`, which will generate a Haskell source file `./GQFC.hs` containing only the code for the library, with none of the paper text.
