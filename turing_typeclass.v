Require Import List. Import ListNotations.

Local Notation "0" := false.
Local Notation "1" := true.

(** A Smallfuck program *)
Inductive prog : Type :=
  | PRight (next : prog)
  | PLeft (next : prog)
  | PFlip (next : prog)
  | PLoop (body : prog) (next : prog)
  | PEnd.

(** An infinite tape, where [cell] is the current cell and [ltape] and [rtape]
    are the cells to the left and right, respectively. *)
Record tape : Type := Tape {
  cell : bool;
  ltape : list bool;
  rtape : list bool;
}.

Class Exec (p : prog) (t : tape) : Type := {
  exec : tape;
}.

#[export] Instance Exec_Right_cons p c lt rc rt
    `{E : Exec p (Tape rc (c :: lt) rt)} :
    Exec (PRight p) (Tape c lt (rc :: rt)) := {
  exec := E.(exec);
}.
#[export] Instance Exec_Right_nil p c lt
    `{E : Exec p (Tape 0 (c :: lt) [])} :
    Exec (PRight p) (Tape c lt []) := {
  exec := E.(exec);
}.

#[export] Instance Exec_Left_cons p c lc lt rt
    `{E : Exec p (Tape lc lt (c :: rt))} :
    Exec (PLeft p) (Tape c (lc :: lt) rt) := {
  exec := E.(exec);
}.
#[export] Instance Exec_Left_nil p c rt
    `{E : Exec p (Tape 0 [] (c :: rt))} :
    Exec (PLeft p) (Tape c [] rt) := {
  exec := E.(exec);
}.

#[export] Instance Exec_Flip p c lt rt
    `{E : Exec p (Tape (negb c) lt rt)} :
    Exec (PFlip p) (Tape c lt rt) := {
  exec := E.(exec);
}.

#[export] Instance Exec_Loop_0 b p lt rt
    `{E : Exec p (Tape 0 lt rt)} :
    Exec (PLoop b p) (Tape 0 lt rt) := {
  exec := E.(exec);
}.
#[export] Instance Exec_Loop_1 b p lt rt
    `{Eb : Exec b (Tape 1 lt rt)}
    `{Ep : Exec (PLoop b p) Eb.(exec)} :
    Exec (PLoop b p) (Tape 1 lt rt) := {
  exec := Ep.(exec);
}.

#[export] Instance Exec_End t : Exec PEnd t := {
  exec := t;
}.

Set Typeclasses Debug.
Definition exec_end `{E : Exec PEnd (Tape 0 [] [])} := E.(exec).
Check exec_end.
Definition exec_right `{E : Exec (PRight PEnd) (Tape 0 [] [])} := E.(exec).
Check exec_right.
Definition exec_nonterm `{E : Exec (PLoop PEnd PEnd) (Tape 1 [] [])} := E.(exec).
Check exec_nonterm.
