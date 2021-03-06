Require Export Coq.Program.Basics Coq.Classes.RelationClasses
        Coq.Lists.List Coq.Arith.PeanoNat
        Coq.micromega.Lia Coq.Arith.Compare_dec.
Export ListNotations.

Section Mapply.
  Context {A : Set}.

  Fixpoint mapply (m : nat) (f : A -> A) (a : A) : A :=
    match m with
    | O   => a
    | S m => f (mapply m f a)
    end.

  Lemma mapply_comm : forall m f a, mapply m f (f a) = f (mapply m f a).
  Proof.
    intro m; induction m as [| m ih];
      intros f a; cbn; f_equal; auto.
  Qed.

  Lemma mapply_id : forall (m : nat) (a : A),
      mapply m (fun a => a) a = a.
  Proof.
    intros m; induction m as [| m ih]; intro a; cbn; auto.
  Qed.
End Mapply.

Lemma mapply_plus : forall m n,
    mapply m S n = m + n.
Proof.
  intro m; induction m as [| m ih];
    intros n; cbn; f_equal; auto.
Qed.

Definition ext (ρ : nat -> nat) (X : nat) : nat :=
  match X with
  | O   => O
  | S n => S (ρ n)
  end.

Lemma mapply_ext : forall n x ρ,
    ext (mapply n ext ρ) (mapply n ext S x) = mapply n ext S (mapply n ext ρ x).
Proof.
  intro n; induction n as [| n ihn];
    intros x ρ; cbn; try reflexivity.
  destruct x as [| x]; cbn; try reflexivity || f_equal; auto.
Qed.

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

Section AccLemmas.
  Local Hint Constructors Acc : core.
  
  Lemma acc_pres : forall A B (f : A -> B) (R : A -> A -> Prop) (Q : B -> B -> Prop),
    (forall a1 a2, R a1 a2 -> Q (f a1) (f a2)) ->
    forall a, Acc Q (f a) -> Acc R a.
  Proof.
    intros A B f R Q Hmap a HQ.
    remember (f a) as fa eqn:Heqfa.
    generalize dependent a.
    induction HQ; intros a Heqfa; subst; eauto.
  Qed.

  Lemma Acc_ind2 :
    forall A B (RA : A -> A -> Prop) (RB : B -> B -> Prop) (P : A -> B -> Prop),
      (forall a b, (forall a', RA a' a -> P a' b) ->
              (forall b', RB b' b -> P a b') -> P a b) ->
      forall a b, Acc RA a -> Acc RB b -> P a b.
  Proof.
    intros A B R Q P H a b HA.
    generalize dependent b.
    induction HA; intros b HB;
      induction HB; eauto.
  Qed.
End AccLemmas.

Definition obind {A B : Set} (o : option A) (ƒ : A -> option B) : option B :=
  match o with
  | None => None
  | Some a => ƒ a
  end.

Notation "o '>>=' f" := (obind o f) (at level 50, left associativity).
Notation "o '>>|' f" := (option_map f o) (at level 50, left associativity).
Notation "'let*' x ':=' c1 'in' c2"
  := (obind c1 (fun x => c2))
       (at level 61, x pattern, 
         format "'let*'  x  ':='  c1  'in' '//' c2", c1 at next level, 
         right associativity).
Notation "'let*' ' x ':=' c1 'in' c2"
  := (obind c1 (fun x => c2))
       (at level 61, x pattern, 
         format "'let*'  ' x  ':='  c1  'in' '//' c2", c1 at next level, 
         right associativity).

Ltac match_some :=
  match goal with
  | h: match ?t with
       | Some _ => _
       | None => None
       end = Some _
    |- _ => destruct t eqn:?; try discriminate
  end.

Ltac some_inv :=
  match goal with
  | h: Some _ = Some _ |- _ => inv h
  end.
