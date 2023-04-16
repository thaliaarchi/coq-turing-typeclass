# Coq typeclass resolution is Turing-complete

The Coq theorem prover has a powerful means of abstraction, typeclasses. To
resolve a typeclass instance, the typechecker performs an unrestricted search
for an instance satisfying those constraints. The steps in this search resemble
the trace of a program execution, and, crucially, it is possible to express
unsatisfiable constraints, which cause an infinite search. This indicates it
should be Turing-complete! Let's prove it!

In this tutorial, I implement Smallfuck using only typeclass instance resolution
in Coq. To my knowledge, this is the first proof of its Turing-completeness.

Read it in [turing_typeclass.v](turing_typeclass.v) or [rendered](https://thaliaarchi.github.io/coq-turing-typeclass/).
