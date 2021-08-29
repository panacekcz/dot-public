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

Section AboutSubstCommut.
  Context `(SC : SubstCommut A).
  Lemma subst_commut' x y w z (X: A):
    x <> w ->
    (y <> w \/ x = z ) ->
    (subst_var x y  (subst_var w z X)) = (subst_var w (z \[x -> y]) (subst_var x y X)).
  Proof.
    intros.
    forwards Hsc: subst_commut; eauto.
    unfold compose in Hsc.
    eapply (fun_eq_1 X) in Hsc. auto.
  Qed.
End AboutSubstCommut.

(* This property is easily proven for variables *)
Instance AvarSubstCommut : SubstCommut AvarAbstractSyntax.
Proof.
  hnf; avar_fun_ext_solver.
  destruct H0; subst; contradiction. 
Qed.

(* 1.1 How to lift this property to types and terms? - SOLVED *)

Section AboutTransformSyntax.
  Context `{OA: Openable A} {FA: FreeVar A} {SA: SubstVar A}.
  Context `{OB: Openable B} {FB: FreeVar B} {SB: SubstVar B}.
  Context {ASB: AbstractSyntax OB FB SB} {ASA: AbstractSyntax OA FA SA}.
  Context {C: Collect ASB ASA} {CC: CollectCompose C} {CR: CollectReflect C}
          {FC: FvCollect C}.
  Context {T: Transform ASB ASA} {TI: TransformId T} {TC: TransformCompose T}
          {OT: OpenTransform T} {ST: SubstTransform T}.
  Context {CT: CollectTransform C T}.

  (** Every TransformSyntax leads to OpenCompose *)
  Section SubstCommut.
    Context {OTC: SubstCommut ASB}.
    Instance TransformSubstCommut : SubstCommut ASA.
    Proof.
      hnf.
      intros.

      apply fun_ext_dep. intros a.
      unfold compose.
      rewrite ? (subst_depth 0).
      rewrite subst_transform.
      rewrite (subst_transform w z).
      rewrite (subst_transform w (z \[ x -> y])).

      rewrite ? fold_compose12. rewrite ? transform_compose.

      eapply f_equal3; auto.
      eapply fun_ext_nondep_2. intros.
      rewrite <- fold_compose12.
      rewrite <- fold_compose12.

      rewrite <- (subst_depth).
      rewrite <- (subst_depth).
      rewrite <- (subst_depth).
      rewrite <- (subst_depth).

      eapply subst_commut'; eauto.
    Qed.
  End SubstCommut.
End AboutTransformSyntax.
Existing Instance TransformSubstCommut.

(* These hints do not seem to help *)
Hint Resolve TransformSubstCommut: core.
Hint Resolve AvarSubstCommut: core.

(* Test that the instance is found for types *)
Lemma test_subst_commut_typ x y z w (t: typ):
  x <> w ->
  (y <> w \/ x = z ) ->
  ((t /[ w -> z]) /[ x -> y]) = ((t /[ x -> y]) /[ w -> z \[ x -> y]]).
Proof.
  intros.
  eapply subst_commut'; eauto.
  (* For some reason, the instance is not found by eauto. *)
  eapply TransformSubstCommut.
Qed.


(* 1.2 - WON'T PURSUE *)
(* I have some other property where there is a precondition referring to the type or term, such as (closed X) *)
(* For simplicity, i show it as a modification of the previous property *)
Class ClosedSubstCommut `(AS : AbstractSyntax A) :=
subst_commut_closed x y w z (X: A):
   closed X ->
   x <> w ->
   (y <> w \/ x = z ) ->
   (subst_var x y (subst_var w z X)) = (subst_var w (z \[x -> y]) (subst_var x y X)).

(* Is it even possible to lift such a property to terms and types using transform and collect? *)




(* Question 2 - SOLVED *)
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


(* NEW CLASS for shifting the index in transform *)
Class TransformShift `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) (T: Transform AS AS'):=
  transform_shift f X n m: transform f X (n + m) = transform (fun X' n' => f X' (n' + m)) X n.

Lemma transform_shift_typ_dec (f : avar -> nat -> avar) :
  (forall (X : typ) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n) /\
  (forall (X : dec) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n).
Proof.
  apply typ_mutind; simpl; intros; try f_equal; auto.
  - rewrite <- H. rewrite Nat.add_succ_l. auto.
  - rewrite <- H0. rewrite Nat.add_succ_l. auto.
Qed.

Instance TypTransformShift : TransformShift TypTransform.
Proof.
  intro. eapply transform_shift_typ_dec.
Qed.
Instance DecTransformShift : TransformShift TypTransform.
Proof.
  intro. eapply transform_shift_typ_dec.
Qed.

Lemma transform_shift_terms (f : avar -> nat -> avar) :
  (forall (X : trm) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n) /\
  (forall (X : lit) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n) /\
  (forall (X : def) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n) /\
  (forall (X : defs) (n m : nat), transform f X (n + m) = transform (fun (X' : avar) (n' : nat) => f X' (n' + m)) X n).
Proof.
  apply trm_mutind; simpl; intros; try f_equal; auto.
  - rewrite <- H0. rewrite Nat.add_succ_l. auto.
  - rewrite <- H0. rewrite Nat.add_succ_l. auto.
  - rewrite <- transform_shift. auto.
  - rewrite <- H. rewrite Nat.add_succ_l. auto.
  - rewrite <- transform_shift. auto.
  - rewrite <- H. rewrite Nat.add_succ_l. auto.
  - rewrite <- transform_shift. auto.
Qed.

Instance TrmTransformShift : TransformShift TrmTransform.
Proof.
  intro. eapply transform_shift_terms.
Qed.
Instance LitTransformShift : TransformShift LitTransform.
Proof.
  intro. eapply transform_shift_terms.
Qed.
Instance DefTransformShift : TransformShift DefsTransform.
Proof.
  intro. eapply transform_shift_terms.
Qed.
Instance DefsTransformShift : TransformShift DefsTransform.
Proof.
  intro. eapply transform_shift_terms.
Qed.


(* Now, we can prove this lemma *)
Lemma typ_bnd_close n x T1:
  close_rec n x (typ_bnd T1) = typ_bnd (close_rec (S n) x T1).
Proof.
  sympl.
  unfold TransformClosing; sympl.
  unfold close_rec, transform, TypTransform.

  eapply f_equal. (* Strips typ_bnd *)
  (* Here we get the goal:
   transform_typ (close_depth_rec n x) T1 1 = transform_typ (close_depth_rec (S n) x) T1 0 *)
  replace 1 with (0 + 1). (* Puts the number into a form that transform_shift understands *)
  rewrite rewrite_transform_typ. (* Folds transform_typ into transform *)
  rewrite transform_shift.
  eapply f_equal3; auto. (* Strips transform *)
  eapply fun_ext_nondep_2.
    intros. unfold close_depth_rec.
    eapply f_equal3; auto. (* Strips close_rec *)
    rewrite Nat.add_succ_l.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    auto.
  (* 0 + 1 *)
  rewrite Nat.add_0_l.
  auto.
Qed.
