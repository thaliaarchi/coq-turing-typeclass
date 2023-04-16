# Coq typeclass resolution is Turing-complete

To resolve a typeclass instance, Coq performs an unrestricted proof search for a
satisfying instance. This proof search can be seen as the trace of a program
execution and when no such instance exists, the search diverges. This indicates
it should be Turing-complete! Let's prove it!

In this tutorial, I implement Smallfuck using only typeclass instance resolution
in Coq. To my knowledge, this is the first proof of its Turing-completeness.

Read it in [turing_typeclass.v](turing_typeclass.v) or [rendered](https://thaliaarchi.github.io/coq-turing-typeclass/).
