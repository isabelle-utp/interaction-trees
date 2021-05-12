# Interaction Trees

[Interactions Trees](https://github.com/DeepSpec/InteractionTrees) (ITrees) are coinductive structures used to represent interactions between a system and its environment in the style of a process algebra.
This repository contains a mechanisation of ITrees in Isabelle/HOL, for the purpose of verifying reactive systems and generating code for animation purposes.
You can find a number of examples under ``examples/``, and in particular the Haskell code can be executed in [GHCi](https://www.haskell.org/ghc/) for animation purposes.

The theories have been developed in [Isabelle2021](https://isabelle.in.tum.de/). You will also need the following dependencies:

* [Optics](https://github.com/isabelle-utp/Optics), branch isabelle2021
* [Shallow Expressions](https://github.com/isabelle-utp/Shallow-Expressions), branch main

You'll need to clone these repositories, and make Isabelle aware of them either with ``isabelle jedit -d dirs`` or editing your ``ROOTS`` file.

As an example animation, you can try ``ghci examples/Buffer_CSP.hs`` and then ``simulate (buffer [])`` to animate a buffer that is initially empty.

