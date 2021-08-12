Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import
        AbstractSyntax GeneralTyping
        InertTightSubtyping
        GeneralToTight TightTyping InvertibleTyping
        RecordAndInertTypes PreciseTyping
        OperationalSemantics Substitution Weakening
        HeapCorrespondence HeapUpdate CanonicalForms
        InertGeneralSubtyping Subenvironments Narrowing Vars.


Generalizable Variables A B.

(* Question 1 *)
(* How to lift properties to term and type syntax *)

(* A property defined as a class, in the same way as OpenCommut is *)
Class SubstCommut `(AS : AbstractSyntax A) :=
subst_commut x y w z:
    x <> w ->
    (y <> w \/ x = z ) ->
    (subst_var x y) ∘ (subst_var w z) = (subst_var w (z \[x -> y])) ∘ (subst_var x y).

(* This property is easily proven for variables *)
Instance AvarSubstCommut : SubstCommut AvarAbstractSyntax.
Proof.
  hnf; avar_fun_ext_solver.
  destruct H0; subst; contradiction. 
Qed.

(* 1.1 How to lift this property to types and terms? *)

(* 1.2 *)
(* I have some other property where there is a precondition referring to the type or term, such as (closed X) *)
(* For simplicity, i show it as a modification of the previous property *)
Class ClosedSubstCommut `(AS : AbstractSyntax A) :=
subst_commut_closed x y w z (X: A):
   closed X ->
   x <> w ->
   (y <> w \/ x = z ) ->
   (subst_var x y (subst_var w z X)) = (subst_var w (z \[x -> y]) (subst_var x y X)).

(* Is it even possible to lift such a property to terms and types using transform and collect? *)




(* Question 2 *)
(* How to prove typ_bnd_close, which shows how closing distributes into typ_bnd? *)

(* Similar lemma for opening typ_bnd proves easily *)
Lemma typ_bnd_open n x T1:
  open_rec n x (typ_bnd T1) = typ_bnd (open_rec (S n) x T1).
Proof.
  simpl. eauto.
Qed.

(* Similar lemma for closing typ_and (where the index does not change) also proves easily *)
Lemma typ_and_close n x T1 T2:
  close_rec n x (typ_and T1 T2) = typ_and (close_rec n x T1) (close_rec n x T2).
Proof.
  simpl. eauto.
Qed.

(* Here, the same approach does not work *)
Lemma typ_bnd_close n x T1:
  close_rec n x (typ_bnd T1) = typ_bnd (close_rec (S n) x T1).
Proof.
  simpl. eauto.
  (* even compute tactic does not help *)
  compute. eauto.
Qed.

