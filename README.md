# termseq

This project aims at developing a termination analysis for languages with symmetric data and codata and proving its soundness.\
Such languages are a [modern approach to intermediate represenations (IR)](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/sequent-calculus-icfp16.pdf) and having a proper termination analysis for an IR is important w.r.t. partial evaluation.
As a byproduct, a soundness proof would be helpful to prove the termination analysis of [Agda](https://github.com/agda) sound.

So far, the project consists of a paper sketch explaining the idea for the termination analysis and a formalization of the involved languages.

## Installation

Just call `make bib` at the top-level of the repo.

## Contributing

Contributions are welcome!
We are glad about any kind of help.
Just use Github Issues and pull requests as you would for any other project.

### Style

If you contribute text, please follow [Dreyer's notes on writing papers](https://people.mpi-sws.org/~dreyer/talks/talk-plmw16.pdf).

## TODO

The most important thing yet to do is coming up with a precise idea of how to prove the suggested termination analysis sound.

Otherwise, besides what is said in the 'Authors:'-notes in the text, what we need next is

- an introduction pitching
  * the use cases
    + partial evaluation
    + Agda soundness
  * the contributions
    + translation from asymmetric to symmetric data/codata
    + formualtion of strict positivity for symmetric data/codata
    + formualtion of structural recursion for symmetric data/codata
    + soundness of the termination analysis based on the size-change termination principle
- a full draft of the formalization by
  * adding text describing the language formalizations
  * formalizing the translation from asymmetric to symmetric data/codata
  * formalizing the termination analysis
- a related work section
