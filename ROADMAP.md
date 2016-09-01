Roadmap
=======

Stage 1
-------

Formalizing semantics of the source language with the proof assistant in use.

Stage 2
-------

Implementing the translation algorithm in some high-level language (i.e.
Haskell or Rust). This stage needs to be separate because it may become
tiresome to debug the program in proof assistants.

The code produced by the algorithm should use as few JavaScript language
constructs as possible.

Stage 3
-------

Formalizing the subset of JavaScript which can be produced by the algorithm.

Stage 4
-------

Formalizing the algorithm, correcting the results of previous stages when
necessary.

