Require Export Coq.Program.Basics Coq.Classes.RelationClasses
        Coq.Lists.List Coq.Arith.PeanoNat
        Coq.micromega.Lia Coq.Arith.Compare_dec.
Export ListNotations.

Infix "$" := apply (at level 41, right associativity).

Ltac inv H := inversion H; subst; clear H.

Ltac compare_destruct :=
  match goal with
  | |- context [le_lt_dec ?a ?b]
    => destruct (le_lt_dec a b) as [? | ?] eqn:?
  | |- context [lt_dec ?a ?b]
    => destruct (lt_dec a b) as [? | ?] eqn:?
  | |- context [lt_eq_lt_dec ?a ?b]
    => destruct (lt_eq_lt_dec a b) as [[? | ?] | ?] eqn:?
  | |- context [match ?n with 0 => _ | S _ => _ end]
    => destruct n as [| ?] eqn:?
  end.
(**[]*)

Ltac compare_destruct_star := repeat (compare_destruct; simpl).

Ltac clean_compare := compare_destruct_star; try lia; auto.

Ltac destroy_arith :=
  intros; simpl; clean_compare;
  try (f_equal; auto 2; lia).

(** * Binary Relations *)

Definition deterministic {A : Type} (R : A -> A -> Prop) : Prop :=
  forall a a1 a2, R a a1 -> R a a2 -> a1 = a2.

Ltac ind_det :=
  match goal with
  | |- deterministic _
    => intros ? ? a2 H1;
      generalize dependent a2;
      induction H1; intros ? H2; inv H2; auto
  end.
(**[]*)

(** Reflexive-Transitive Closure of a Relation. *)

Reserved Notation "a1 '~~>' a2" (at level 40).

Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_closure a :
    a ~~>  a
| trans_closure a1 a2 a3 :
    R a1 a2 ->
    a2 ~~>  a3 ->
    a1 ~~>  a3
where "a1 '~~>' a2" := (refl_trans_closure _ a1 a2).
(**[]*)

Section ReflTransClosureProp.
  Context {A : Type}.
  Variable (R : A -> A -> Prop).

  Local Hint Constructors refl_trans_closure : core.
  
  Global Instance refl_trans_closure_reflexive
    : Reflexive (refl_trans_closure R).
  Proof using Type. auto 2. Qed.

  Lemma inject_trans_closure : forall a1 a2,
      R a1 a2 -> refl_trans_closure R a1 a2.
  Proof using Type. eauto 2. Qed.

  Global Instance refl_trans_closure_transitive
    : Transitive (refl_trans_closure R).
  Proof using Type.
    intros x y z Hxy Hyz; generalize dependent z.
    induction Hxy; intros z Hyz; eauto 3.
  Qed.

  Lemma trans_closure_r : forall a1 a2 a3,
      R a2 a3 ->
      refl_trans_closure R a1 a2 ->
      refl_trans_closure R a1 a3.
  Proof.
    intros a1 a2 a3 HR H12.
    transitivity a2; eauto 2.
  Qed.

  (** "Halting" condition. *)
  Definition halts_R (a : A) : Prop :=
    exists a', refl_trans_closure R a a' /\ forall a'', ~ R a' a''.
End ReflTransClosureProp.

Section NthError.
  Context {A : Type}.
  
  Lemma nth_error_nil : forall n, nth_error (@nil A) n = None.
  Proof. intros []; reflexivity. Qed.

  Hint Rewrite nth_error_nil : core.

  Lemma nth_error_length : forall (l : list A) n a,
      nth_error l n = Some a -> n < length l.
  Proof.
    intro l; induction l as [| h t IHt];
      intros [| n]; simpl; intros a H;
        autorewrite with core in *; try discriminate; try lia.
    apply IHt in H. lia.
  Qed.

  Lemma nth_error_app_plus : forall (l l' : list A) n,
      nth_error (l ++ l') (length l + n) = nth_error l' n.
  Proof.
    intros l l' n.
    rewrite nth_error_app2 by lia.
    f_equal; lia.
  Qed.

  Lemma nth_map : forall B (f : A -> B) l n a b,
      n < length l ->
      nth n (map f l) b = f (nth n l a).
  Proof.
    induction l as [| h t IHt];
      intros [| n] a b; simpl; intros; try lia; auto.
    apply IHt; lia.
  Qed.

  Lemma length_nth_error : forall (l : list A) n,
      n < length l -> exists a, nth_error l n = Some a.
  Proof.
    intro l; induction l as [| h t IHt];
      intros [| n] H; simpl in *; try lia; eauto.
    apply IHt. lia.
  Qed.
End NthError.

Section Forall2.
  Variables A B : Type.
  Variable R : A -> B -> Prop.
  
  Lemma Forall2_length : forall a b,
    Forall2 R a b -> length a = length b.
  Proof.
    intros a b H; induction H; simpl; auto.
  Qed.
  
  Lemma Forall2_impl : forall (Q : A -> B -> Prop) a b,
      (forall a b, R a b -> Q a b) ->
      Forall2 R a b -> Forall2 Q a b.
  Proof.
    intros Q a b H HP;
      induction HP; auto.
  Qed.

  Lemma Forall2_nth_error : forall la lb,
      Forall2 R la lb ->
      forall n a b, nth_error la n = Some a ->
               nth_error lb n = Some b ->
               R a b.
  Proof.
    intros la lb HR; induction HR;
      intros [| n] a b Hntha Hnthb;
      simpl in *; try discriminate.
    - inv Hntha; inv Hnthb. assumption.
    - pose proof IHHR _ _ _ Hntha Hnthb.
      assumption.
  Qed.
End Forall2.
