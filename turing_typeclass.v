Require Import List. Import ListNotations.

(** * Coq typeclass resolution is Turing-complete

    To resolve a typeclass instance, Coq performs an unrestricted proof search
    for a satisfying instance. This proof search can be seen as the trace of a
    program execution and when no such instance exists, the search diverges.
    This indicates it should be Turing-complete! Let's prove it!

    (The source code for this tutorial is at
    #<a href="https://github.com/thaliaarchi/coq-turing-typeclass">github.com/thaliaarchi/coq-turing-typeclass</a>#.) *)

(** ** Typeclasses

    A typeclass is essentially an interface associated with a type.

    In Coq, [`{Tc}] is syntax for a typeclass constraint and is equivalent to
    [{A : Type} {I : Tc}], that is, "[A] is some type, such that an instance [I]
    of typeclass [Tc] exists for [A]". For example, the typeclass [InjTyp T U]
    in the standard library represents a conversion from some type [T] to some
    type [U]. Proofs with linear integer arithmetic use
    [{T : Type} `{InjTyp T Z}] to convert from some type [T] to the built-in
    signed integer type [Z].

    Typeclasses were first introduced in Haskell and have since been adopted by
    many other languages, including in Rust as traits. However, because Coq is
    dependently-typed, its typeclass constraints can also contain arbitrary
    types and values, making making it strictly more powerful than typeclasses
    in other languages. This is what makes it Turing-complete.

    For a more in-depth tutorial on typeclasses, see the
    #<a href="https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html">Typeclasses</a>#
    chapter in the fantastic Software Foundations series. The section on
    non-termination and the advice from experts are particularly relevant to
    this. *)

(** ** Smallfuck

    To prove Turing-completeness, it is sufficient to implement a
    Turing-complete language.

    I model the semantics of #<a href="https://esolangs.org/wiki/Smallfuck">Smallfuck</a>#,
    a subset of Brainfuck, using typeclass instances. Smallfuck has a tape of
    bits and can move the cell pointer left or right, flip the current cell, and
    loop. I/O and a more complex cell type are not needed to demonstrate
    Turing-completeness, but you could see how that would be modelled in my
    #<a href="https://github.com/thaliaarchi/bfcoq">bfcoq</a># project. *)

(** [prog] represents a Smallfuck program:

    - [PRight] ([>]) moves the tape right
    - [PLeft] ([<]) moves the tape left
    - [PFlip] ([*]) flips the current cell
    - [PLoop] ([[...]]) repeats while the current cell is 1
    - [PEnd] is a no-op used at the end of a loop or program *)

Inductive prog : Type :=
  | PRight (next : prog)
  | PLeft (next : prog)
  | PFlip (next : prog)
  | PLoop (body : prog) (next : prog)
  | PEnd.

(** [tape] is an infinite tape, where [cell] is the current cell and [ltape] and
    [rtape] are the cells to the left and right, respectively. *)

Record tape : Type := Tape {
  cell : bool;
  ltape : list bool;
  rtape : list bool;
}.

(** Let's define a shorthand for booleans. *)

Local Notation "0" := false.
Local Notation "1" := true.

(** ** Small-step semantics

    To execute a Smallfuck program, we map an initial tape to a final tape. That
    can be modeled as a typeclass [Exec], that takes a program [p] and initial
    and final tapes [t] and [t'], and provides a function [exec] that returns
    [t']. *)

Class Exec (p : prog) (t t' : tape) : Type := {
  exec := t';
}.

(** I then define instances of [Exec] for each operation in big-step semantics
    style.

    [PEnd] is the simplest to model; it takes a tape [t] and maps it to
    itself. *)

#[export] Instance Exec_End t :
  Exec PEnd t t := {}.

(** [PFlip] negates the current cell.

    Intuitively, this definition states that if an instance of [Exec] exists for
    the rest of the program, starting with the flipped tape and producing some
    tape [t'], then we can apply [PFlip]. *)

#[export] Instance Exec_Flip p c lt rt t'
  `{Exec p (Tape (negb c) lt rt) t'} :
  Exec (PFlip p) (Tape c lt rt) t' := {}.

(** [PRight] has two cases: When the tape has at least one cell to the left,
    shift that cell to the current and the old current to the right. When the
    left tape is empty, use [0] as the new current cell. *)

#[export] Instance Exec_Right_cons p c lt rc rt t'
  `{Exec p (Tape rc (c :: lt) rt) t'} :
  Exec (PRight p) (Tape c lt (rc :: rt)) t' := {}.
#[export] Instance Exec_Right_nil p c lt t'
  `{Exec p (Tape 0 (c :: lt) []) t'} :
  Exec (PRight p) (Tape c lt []) t' := {}.

(** Likewise for [PLeft]. *)

#[export] Instance Exec_Left_cons p c lc lt rt t'
  `{Exec p (Tape lc lt (c :: rt)) t'} :
  Exec (PLeft p) (Tape c (lc :: lt) rt) t' := {}.
#[export] Instance Exec_Left_nil p c rt t'
  `{Exec p (Tape 0 [] (c :: rt)) t'} :
  Exec (PLeft p) (Tape c [] rt) t' := {}.

(** Finally, [PLoop] has two cases: When the current cell is [0], skip the body
    and execute the next instruction. When the current cell is [1], execute the
    body, then repeat the loop. [Exec_Loop_1] requires two instances, for
    executing the body once and for executing the loop again. *)

#[export] Instance Exec_Loop_0 b p lt rt t'
  `{Exec p (Tape 0 lt rt) t'} :
  Exec (PLoop b p) (Tape 0 lt rt) t' := {}.
#[export] Instance Exec_Loop_1 b p lt rt t' t''
  `{Exec b (Tape 1 lt rt) t'}
  `{Exec (PLoop b p) t' t''} :
  Exec (PLoop b p) (Tape 1 lt rt) t'' := {}.

(** ** Execution

    Now let's execute programs by typechecking! First, enable typeclass
    debugging, so we can inspect the search path. *)

Set Typeclasses Debug.

(** As expected, this typechecks, because [>] shifts the tape [1(1)01] right to
    [11(0)1]: *)

Definition exec_right_verify
  `{E : Exec (PRight PEnd) (Tape 1 [1] [0; 1]) (Tape 0 [1; 1] [1])} := E.
Check exec_right_verify.

(** However, give it an impossible result and it cannot find an instance: *)

Definition exec_right_bad
  `{E : Exec (PRight PEnd) (Tape 1 [1] [0; 1]) (Tape 0 [] [])} := E.
Check exec_right_bad.

(** More usefully, we can generalize it to any tape [t] and let it infer the
    final tape after execution: *)

Definition exec_right t
  `{E : Exec (PRight PEnd) t} := E.
Check exec_right (Tape 1 [1] [0; 1]).

(** We can execute loops too, like [>*>*[*<]]: *)

Definition exec_rr_back t
  `{E : Exec (PRight (PFlip (PRight (PFlip
              (PLoop (PFlip (PLeft PEnd)) PEnd))))) t} := E.
Check exec_rr_back (Tape 0 [] [1]).

(** Non-terminating programs like [[]] and [>*[>*]] work too. For the latter, it
    cannot resolve an instance for any initial tape.

    Each iteration of the loop generates for a fresh intermediate value for the
    tape, which ensures a revisited state will not resolve to the same
    instance. *)

Definition exec_loop_nonterm
  `{E : Exec (PLoop PEnd PEnd) (Tape 1 [] [])} := E.
Fail Timeout 1 Check exec_loop_nonterm.

Definition exec_loop_r_nonterm
  `{E : Exec (PRight (PFlip (PLoop (PRight (PFlip PEnd)) PEnd)))} := E.
Fail Timeout 1 Check exec_loop_r_nonterm.

(** And finally, a program that writes "Hallo, Welt!" in binary to the tape,
    [>*>>>*>>>>>*>*>>>>>*>>*>*>>*>*>>>>*>*>>*>*>>>>*>*>>*>*>*>*>>>*>>*>*>>>
    >>*>>>>>>>*>>*>>*>*>*>>*>*>>>*>>*>>*>*>>*>*>>>>*>*>*>>*>>>>>*>>>>>*>]: *)

Definition exec_hworld
  `{E : Exec (PRight (PFlip (PRight (PRight (PRight (PFlip (PRight (PRight
             (PRight (PRight (PRight (PFlip (PRight (PFlip (PRight (PRight
             (PRight (PRight (PRight (PFlip (PRight (PRight (PFlip (PRight
             (PFlip (PRight (PRight (PFlip (PRight (PFlip (PRight (PRight
             (PRight (PRight (PFlip (PRight (PFlip (PRight (PRight (PFlip
             (PRight (PFlip (PRight (PRight (PRight (PRight (PFlip (PRight
             (PFlip (PRight (PRight (PFlip (PRight (PFlip (PRight (PFlip
             (PRight (PFlip (PRight (PRight (PRight (PFlip (PRight (PRight
             (PFlip (PRight (PFlip (PRight (PRight (PRight (PRight (PRight
             (PFlip (PRight (PRight (PRight (PRight (PRight (PRight (PRight
             (PFlip (PRight (PRight (PFlip (PRight (PRight (PFlip (PRight
             (PFlip (PRight (PFlip (PRight (PRight (PFlip (PRight (PFlip
             (PRight (PRight (PRight (PFlip (PRight (PRight (PFlip (PRight
             (PRight (PFlip (PRight (PFlip (PRight (PRight (PFlip (PRight
             (PFlip (PRight (PRight (PRight (PRight (PFlip (PRight (PFlip
             (PRight (PFlip (PRight (PRight (PFlip (PRight (PRight (PRight
             (PRight (PRight (PFlip (PRight (PRight (PRight (PRight (PRight
             (PFlip (PRight PEnd)))))))))))))))))))))))))))))))))))))))))))
             ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             ))))))))))))))))))))))))))))))))) (Tape 0 [] [])} := E.
Check exec_hworld.
Compute rev exec_hworld.(exec).(ltape).
