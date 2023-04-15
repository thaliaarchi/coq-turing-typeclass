Require Import List. Import ListNotations.

Local Notation "0" := false.
Local Notation "1" := true.

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

Class Exec (p : prog) (t t' : tape) : Type := {
  exec := t';
}.

#[export] Instance Exec_Right_cons p c lt rc rt t'
  `{Exec p (Tape rc (c :: lt) rt) t'} :
  Exec (PRight p) (Tape c lt (rc :: rt)) t' := {}.
#[export] Instance Exec_Right_nil p c lt t'
  `{Exec p (Tape 0 (c :: lt) []) t'} :
  Exec (PRight p) (Tape c lt []) t' := {}.

#[export] Instance Exec_Left_cons p c lc lt rt t'
  `{Exec p (Tape lc lt (c :: rt)) t'} :
  Exec (PLeft p) (Tape c (lc :: lt) rt) t' := {}.
#[export] Instance Exec_Left_nil p c rt t'
  `{Exec p (Tape 0 [] (c :: rt)) t'} :
  Exec (PLeft p) (Tape c [] rt) t' := {}.

#[export] Instance Exec_Flip p c lt rt t'
  `{Exec p (Tape (negb c) lt rt) t'} :
  Exec (PFlip p) (Tape c lt rt) t' := {}.

#[export] Instance Exec_Loop_0 b p lt rt t'
  `{Exec p (Tape 0 lt rt) t'} :
  Exec (PLoop b p) (Tape 0 lt rt) t' := {}.
#[export] Instance Exec_Loop_1 b p lt rt t' t''
  `{Exec b (Tape 1 lt rt) t'}
  `{Exec (PLoop b p) t' t''} :
  Exec (PLoop b p) (Tape 1 lt rt) t'' := {}.

#[export] Instance Exec_End t :
  Exec PEnd t t := {}.

Set Typeclasses Debug.

(* empty program *)
Definition exec_end
  `{E : Exec PEnd (Tape 0 [] [])} := E.
Compute exec_end.

(* > *)
Definition exec_right
  `{E : Exec (PRight PEnd) (Tape 0 [] [])} := E.
Check exec_right.

(* >*>*[*<] *)
Definition exec_rr_loop_l
  `{E : Exec (PRight (PFlip (PRight (PFlip (PLoop (PFlip (PLeft PEnd)) PEnd)))))
             (Tape 0 [] [])} := E.
Check exec_rr_loop_l.

(* [] *)
Definition exec_loop_nonterm
  `{E : Exec (PLoop PEnd PEnd) (Tape 1 [] [])} := E.
Fail Timeout 1 Check exec_loop_nonterm.

(* >*[>*] *)
Definition exec_r_loop_r_nonterm
  `{E : Exec (PRight (PFlip (PLoop (PRight (PFlip PEnd)) PEnd)))} := E.
Fail Timeout 1 Check exec_r_loop_r_nonterm.

(* "Hallo, Welt!"
   >*>>>*>>>>>*>*>>>>>*>>*>*>>*>*>>>>*>*>>*>*>>>>*>*>>*>*>*>*>>>*>>*>*>>>
   >>*>>>>>>>*>>*>>*>*>*>>*>*>>>*>>*>>*>*>>*>*>>>>*>*>*>>*>>>>>*>>>>>*> *)
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
Compute (rev exec_hworld.(exec).(ltape)).
