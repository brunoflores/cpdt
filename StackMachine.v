Require Import Bool Arith List Lib.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* ---------- Source language of our compiler ------------- *)

(* Syntax of the source language. *)
Inductive binop : Set := Plus | Times.
(* Use Set to signal as a constituent of programs. *)

(* Our type of arithmetic expressions. *)
Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(* What the programs mean. *)
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

Eval simpl in expDenote (Const 42).
Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

(* ---------- Target language of our compiler ------------- *)
