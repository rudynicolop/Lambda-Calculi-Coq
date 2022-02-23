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

(** List helpers. *)

Section List.
  Context {A : Set}.

  Fixpoint Has (a : A) (Γ : list A) : Set :=
    match Γ with
    | []    => Empty_set
    | h :: Δ => ((h = a) + Has a Δ)%type
    end.

  Variant zilch : list A -> Prop := zilch_nil : zilch [].
  
  Definition lookup :
    forall {Γ : list A} {n : nat},
      n < length Γ -> A.
  Proof.
    refine
      (fix F Γ n HnΓ :=
         match Γ as Γ' return Γ = Γ' -> A with
         | []
           => fun HΓΓ' => _
         | a :: Δ
         => fun HΓΓ' =>
             match n as n' return n = n' -> A with
             | O   => fun _ => a
             | S k => fun Hnn' => F Δ k _
             end eq_refl
         end eq_refl).
    - inv HΓΓ'; cbn in *; lia.
    - subst; cbn in *; lia.
  Defined.
  
  (* Require Import Extraction.
     Recursive Extraction lookup. *)

  Definition length_nth_error' :
    forall {l : list A} {n : nat},
      n < length l -> { a | nth_error l n = Some a }.
  Proof.
    refine
    (fix F l n Hnl :=
       match
         l as l'
         return
         l = l' -> { a | nth_error l n = Some a } with
       | [] => fun H => _
       | h :: t
         => fun H =>
             match
               n as n'
               return
               n = n' -> { a | nth_error l n = Some a } with
             | O
               => fun _ => @exist _ _ h _
             | S k
               => fun Hnn' =>
                   match F t k _ with
                   | exist _ a' Hk => @exist _ _ a' _
                   end
             end eq_refl
       end eq_refl); subst; cbn in *;
      lia || reflexivity || assumption.
  Defined.


  Definition nth_error_lookup :
    forall {Γ : list A} {n : nat} (H : n < length Γ),
      nth_error Γ n = Some (lookup H).
  Proof.
    intro l; induction l as [| a l IHl];
      intros [| n] H; cbn in *;
        try lia; eauto using Lt.lt_S_n.
  Defined.

  Definition ext' : forall {Γ Δ},
      (forall a, Has a Γ -> Has a Δ) ->
      forall b a, Has a (b :: Γ) -> Has a (b :: Δ).
  Proof.
    refine
      (fun l d f b a H =>
         match l as l' return l = l' -> Has a (b :: d) with
         | [] => fun Hl => inl _
         | h :: t
           => fun Hl =>
               match H with
               | inl Hh => inl Hh
               | inr Ht => inr (f _ Ht)
               end
         end eq_refl); subst; cbn in *.
    destruct H as [H | H]; subst; reflexivity || contradiction.
  Defined.

  Definition Has_nth_error : forall {Γ a},
      Has a Γ -> { n | nth_error Γ n = Some a}.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a Hal; cbn in *; try contradiction.
    destruct Hal as [Hha | Hat]; subst.
    - refine (exist _ 0 _); reflexivity.
    - apply IHt in Hat as [k Hk].
      refine (exist _ (S k) _); assumption.
  Defined.

  Definition nth_error_Has : forall {Γ a n},
      nth_error Γ n = Some a -> Has a Γ.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a [| n] Hnth; cbn in *; try discriminate.
    - inv Hnth; left; reflexivity.
    - apply IHt in Hnth; right; assumption.
  Defined.

  Definition nth_error_Has' : forall {Γ a},
      {n | nth_error Γ n = Some a} -> Has a Γ.
  Proof.
    intros l a [n H]; exact (nth_error_Has H).
  Defined.

  Fail Definition nth_error_Has : forall {Γ a},
      Has a Γ <-> {n | nth_error Γ n = Some a}.
  
  Definition ext : forall {Γ Δ : list A},
      (forall a, {n | nth_error Γ n = Some a} ->
              {k | nth_error Δ k = Some a}) ->
      forall b a, {n | nth_error (b :: Γ) n = Some a} ->
               {k | nth_error (b :: Δ) k = Some a}.
  Proof.
    intros l d f b a Hab.
    apply Has_nth_error.
    apply nth_error_Has' in Hab.
    pose proof (fun a H => nth_error_Has' (f a (Has_nth_error H))) as H.
    eauto using ext'.
  Defined.
End List.
