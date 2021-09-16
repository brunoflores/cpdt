Require Import Bool Arith List Lib.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

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
