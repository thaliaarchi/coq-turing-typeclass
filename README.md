# Coq typeclass resolution is Turing-complete

To resolve a typeclass instance, Coq performs an unrestricted proof search for a
satisfying instance. This proof search can be seen as the trace of a program
execution and when no such instance exists, the search diverges. This indicates
it should be Turing-complete! Let's prove it!

I model the semantics [Smallfuck](https://esolangs.org/wiki/Smallfuck), a
Turing-complete subset of Brainfuck, using typeclass instances. Smallfuck has
four commands: `>` moves the tape right, `<` moves the tape left, `*` flips the
current cell, and `[ … ]` executes its body while the cell is 1. I/O and a more
complex cell type are not needed to demonstrate Turing-completeness (for
demonstration of modelling full Brainfuck in Coq, though, see my
[bfcoq](https://github.com/thaliaarchi/bfcoq) project).

```coq
(** A Smallfuck program *)
Inductive prog : Type :=
  | PRight (next : prog) (* > move the tape right *)
  | PLeft (next : prog) (* < move the tape left *)
  | PFlip (next : prog) (* * flip the current cell *)
  | PLoop (body : prog) (next : prog) (* [ … ] repeat while the cell is 1 *)
  | PEnd.

(** An infinite tape, where [cell] is the current cell and [ltape] and [rtape]
    are the cells to the left and right, respectively. *)
Record tape : Type := Tape {
  cell : bool;
  ltape : list bool;
  rtape : list bool;
}.
```

A typeclass essentially an interface associated with a type. In Coq, `` `{Tc} ``
is syntax a class constraint. It is syntax sugar for `{A : Type} {I : Tc}`, that
is, “`A` is some type, such that an instance `I` of typeclass `Tc` exists for
`A`”. Because Coq is dependently-typed a class constraint can also contain
arbitrary types and values. For example, the typeclass `InjTyp T U` represents a
conversion from some type `T` to some type `U`. Coq uses
`` {T : Type} `{InjTyp T Z} `` to convert from some type `T` to the built-in
signed integer type `Z`, for use in proofs with linear integer arithmetic.

We want to execute a Smallfuck program, that maps a given initial tape to a
final tape. That can be modeled as a typeclass `Exec`, that takes a program `p`
and initial and final tapes `t` and `t'`, and provides a function `exec` that
returns `t'`.

```coq
Class Exec (p : prog) (t t' : tape) : Type := {
  exec := t';
}.
```

I then define instances of `Exec` for each operation in big-step semantics
style. The end of a program is the simplest to model; it takes a tape `t` and
maps it to itself:

```coq
Instance Exec_End t :
  Exec PEnd t t := {}.
```

Moving right has two cases: When the left tape has at least one cell, set it to
the current and move the old current to the right. When the left tape is empty,
use `0` as the new current cell.

```coq
#[export] Instance Exec_Right_cons p c lt rc rt t'
  `{Exec p (Tape rc (c :: lt) rt) t'} :
  Exec (PRight p) (Tape c lt (rc :: rt)) t' := {}.
#[export] Instance Exec_Right_nil p c lt t'
  `{Exec p (Tape 0 (c :: lt) []) t'} :
  Exec (PRight p) (Tape c lt []) t' := {}.
```

Similarly for moving left.

Flipping simply negates the current cell:

```coq
#[export] Instance Exec_Flip p c lt rt t'
  `{Exec p (Tape (negb c) lt rt) t'} :
  Exec (PFlip p) (Tape c lt rt) t' := {}.
```

Finally, a loop has two cases: When the current cell is `0`, skip the body of
the loop and execute the next remainder. When the current cell is `1`, execute
the body, then repeat the loop.

```coq
#[export] Instance Exec_Loop_0 b p lt rt t'
  `{Exec p (Tape 0 lt rt) t'} :
  Exec (PLoop b p) (Tape 0 lt rt) t' := {}.
#[export] Instance Exec_Loop_1 b p lt rt t' t''
  `{Exec b (Tape 1 lt rt) t'}
  `{Exec (PLoop b p) t' t''} :
  Exec (PLoop b p) (Tape 1 lt rt) t'' := {}.
```

It can execute programs by resolving the typeclass instance for a given program
and initial tape. If the initial tape is omitted, it functions as an abstract
interpreter, producing a function from tape to tape!

Coq typeclasses are strictly more powerful than typeclasses in Haskell (the
progenitor of typeclasses) and traits in Rust.

https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html
