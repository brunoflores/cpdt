Require Import Bool Arith List Lib.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* ---------- Source language of our compiler ------------- *)

Inductive type : Set := Nat | Bool.

(* Map types of object language to Coq types. *)
Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

(* Syntax of the source language. *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool (* Polymorphism: allow equality of any two values of any type, as long as they have the same type. *)
| TLt : tbinop Nat Nat Bool.

(* Interpret with standard library. *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => beq_nat
  | TEq Bool => eqb
  | TLt => leb
  end.

(* Our type of arithmetic expressions. *)
Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

(* Evaluate examples. *)
Eval simpl in texpDenote (TNConst 41).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

(* ---------- Target language of our compiler ------------- *)

(* Stack types classify sets of possible stacks. *)
Definition tstack := list type.

(* Instructions in terms of stack types.
   Every instruction's type tells what initial stack type it expects and
   what final stack type it will produce. *)
Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
    tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

(* Stack machine programs must guarantee that intermediate stack types
   match within a program. *)
Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
    tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

(* Value stacks at runtime. *)
Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n ,s)
  | TiBConst _ b => fun s => (b, s)
  | TiBinop _ _ _ _ b => fun s =>
                           let '(arg1, (arg2, s')) := s in
                           ((tbinopDenote b) arg1 arg2, s')
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
  | TNil _ => fun s => s
  | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(* ---------- Compiler definition ------------- *)

(* Translation. *)

(* Helper for concatenating two stack machine programs. *)
Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
  | TNil _ => fun p' => p'
  | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TiNConst _ n) (TNil _)
  | TBConst b => TCons (TiBConst _ b) (TNil _)
  | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _) (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

(* Run some compiled programs. *)

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.
Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.
Eval simpl in tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.
Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) nil) tt.

(* Show translation correctness. *)

(* Strategy: In addition to the source expression and its type,
   we quantify over an initial stack type and a stack compatible with it.
   Running the compilation of the program starting from that stack,
   we should arrive at a stack that differs only in having the program's
   denotation pushed onto it. *)
Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
    tprogDenote (tcompile e ts) s = (texpDenote e, s).
Abort.

(* Analogue to the [app_assoc_reverse]. *)
Lemma tconcat_corret : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts),
    tprogDenote (tconcat p p') s = tprogDenote p' (tprogDenote p s).
Proof.
  induction p; crush.
Qed.

(* Register lemma to be used by the brute-force script. *)
Hint Rewrite tconcat_corret.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
    tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
    tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
Proof.
  crush.
Qed.
