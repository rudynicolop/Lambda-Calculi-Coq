Require Export Lambda.SimpleTypes.

(** * Dependently Typed Lambda Calculus. *)

(** Inspired by
    Programming Language Foundations in Agda. *)

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

(** De Bruijn syntax. *)

Declare Scope term_scope.
Delimit Scope term_scope with term.

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term (Γ : list type) : type -> Set :=
| Id (n : nat) (τ : type) :
    nth_error Γ n = Some τ ->
    Γ ⊢ τ
| Abs (τ τ' : type) :
    τ :: Γ ⊢ τ' ->
    Γ ⊢ τ → τ'
| App (τ τ' : type) :
    Γ ⊢ τ → τ' ->
    Γ ⊢ τ ->
    Γ ⊢ τ'
where "Γ '⊢' τ" := (term Γ τ) : term_scope.

Local Hint Constructors term : core.

Definition term_of_id :
  forall {Γ : list type} (n : nat) (H : n < length Γ),
    (Γ ⊢ lookup H)%term := ltac:(eauto using nth_error_lookup).

Definition term_of_nth_error
           {Γ τ} (H : {n | nth_error Γ n = Some τ})
  : (Γ ⊢ τ)%term :=
  match H with
  | exist _ _ Hn => Id _ _ _ Hn
  end.

Definition App_eq
           (Γ : list type) (τ ρ σ : type)
           (t₁ : (Γ ⊢ τ → ρ)%term) (t₂ : (Γ ⊢ σ)%term)
  : τ = σ -> (Γ ⊢ ρ)%term.
Proof.
  intros H; subst; exact (App _ _ _ t₁ t₂).
Defined.

Local Hint Resolve App_eq : core.

Definition App_lookup
           (Γ : list type) (n : nat) (H : n < length Γ) (τ ρ : type)
           (t₁ : (Γ ⊢ lookup H)%term) (t₂ : (Γ ⊢ τ)%term) :
  lookup H = τ → ρ -> (Γ ⊢ ρ)%term.
Proof.
  intros Heq; rewrite Heq in t₁; eauto using App.
Defined.

Local Hint Resolve App_lookup : core.

Notation "'ID' x"
  := (Id _ x _)
       (at level 10, no associativity) : term_scope.
Notation "'`λ' t"
  := (Abs _ _ _ t)
       (at level 15, right associativity) : term_scope.
Notation "'λ' τ '⇒' t"
  := (Abs _ τ _ t)
       (at level 15, right associativity) : term_scope.
Notation "'λ' τ '↣' .. '↣' ρ '⇒' t"
  := (Abs _ τ _ .. (Abs _ ρ _ t) ..)
       (at level 15, right associativity) : term_scope.
Notation "x '⋅' y"
  := (App _ _ _ x y)
       (at level 14, left associativity) : term_scope.

Set Warnings "-non-reversible-notation".
Notation "'#' n"
  := (ltac:(refine (term_of_id n _); cbn; lia))
       (at level 10, no associativity) : term_scope.
Notation "∫ t"
  := (ltac:(refine (Abs _ _ _ _ t); cbn; eauto))
       (at level 15, right associativity) : term_scope.
Notation "x '`⋅' y"
  := (ltac:(refine (App _ _ _ x y); reflexivity))
       (at level 14, left associativity) : term_scope.
Set Warnings "non-reversible-notation".

Fixpoint Rename
         {Γ Δ}
         (f: forall τ, {n | nth_error Γ n = Some τ} ->
                  {k | nth_error Δ k = Some τ})
         {σ} (t: (Γ ⊢ σ)%term) : (Δ ⊢ σ)%term :=
  match t with
  | Id _ _ _ Hm     => term_of_nth_error (f _ (exist _ _ Hm))
  | Abs _ ρ _ t'    => (`λ Rename (ext f ρ) t')%term
  | App _ _ _ t₁ t₂ => (Rename f t₁ ⋅ Rename f t₂)%term
  end.

Definition exts' : forall {Γ Δ},
    (forall τ, Has τ Γ -> (Δ ⊢ τ)%term) ->
    forall {ρ σ}, Has σ (ρ :: Γ) -> (ρ :: Δ ⊢ σ)%term.
Proof.
  cbn; intros Γ Δ f ρ σ [H | H]; subst.
  - refine (Id _ 0 _ _); reflexivity.
  - refine (Rename _ (f _ H)).
    intros τ Hτ.
    apply nth_error_Has' in Hτ.
    apply Has_nth_error; cbn.
    right; assumption.
Defined.

Definition exts : forall {Γ Δ},
    (forall τ, {n | nth_error Γ n = Some τ} -> (Δ ⊢ τ)%term) ->
    forall ρ σ, {k | nth_error (ρ :: Γ) k = Some σ} -> (ρ :: Δ ⊢ σ)%term.
Proof.
  intros Γ Δ f ρ σ H.
  apply nth_error_Has' in H.
  pose proof (fun t H => f t (Has_nth_error H)) as f'.
  exact (exts' f' H).
Defined.

Fixpoint subs
         {Γ Δ}
         (f : forall τ, {n | nth_error Γ n = Some τ} -> (Δ ⊢ τ)%term)
         {σ} (t : (Γ ⊢ σ)%term) : (Δ ⊢ σ)%term :=
  match t with
  | Id _ _ _ Hn => f _ (exist _ _ Hn)
  | Abs _ ρ _ t' => (`λ subs (exts f ρ) t')%term
  | App _ _ _ t₁ t₂ => (subs f t₁ ⋅ subs f t₂)%term
  end.

Definition sub
           {Γ τ σ}
           (body : (τ :: Γ ⊢ σ)%term) (arg : (Γ ⊢ τ)%term)
  : (Γ ⊢ σ)%term.
Proof.
  refine (subs _ body).
  intros ρ [n Hρ].
  destruct n as [| n]; cbn in *.
  - inv Hρ. apply arg.
  - eauto using term_of_nth_error.
Defined.

Notation "x '[[' y ']]'"
  := (sub x y) (at level 12, no associativity) : term_scope.

Reserved Notation "x '-->' y" (at level 80, no associativity).

Inductive bred {Γ} : forall {τ}, (Γ ⊢ τ)%term -> (Γ ⊢ τ)%term -> Prop :=
| bred_bred τ τ' (t₁ : (τ :: Γ ⊢ τ')%term) t₂ :
    ((`λ t₁) ⋅ t₂)%term --> (t₁ [[ t₂ ]])%term
| bred_abs τ τ' (t t' : (τ :: Γ ⊢ τ')%term) :
    t -->  t' ->
    (`λ t)%term --> (`λ t')%term
| bred_app_l τ τ' (t₁ t₁' : (Γ ⊢ τ → τ')%term) t₂ :
    t₁ -->  t₁' ->
    (t₁ ⋅ t₂)%term -->  (t₁' ⋅ t₂)%term
| bred_app_r τ τ' (t₁ : (Γ ⊢ τ → τ')%term) t₂ t₂' :
    t₂ -->  t₂' ->
    (t₁ ⋅ t₂)%term -->  (t₁ ⋅ t₂')%term
where "x '-->' y" := (bred x y) : type_scope.

Local Hint Constructors bred : core.

Variant value {Γ} : forall {τ}, (Γ ⊢ τ)%term -> Prop :=
  Abs_value τ τ' (t : (τ :: Γ ⊢ τ')%term) : value (`λ t)%term.

Lemma value_ex : forall Γ τ (t : (Γ ⊢ τ)%term),
    value t ->
    exists ρ σ (bdy : (ρ :: Γ ⊢ σ)%term), t ~= (`λ bdy)%term.
Proof.
  intros Γ τ t Hv; inv Hv; eauto.
Qed.

Local Hint Constructors value : core.

Definition Type_of {A : Type} (_ : A) :  Type := A.

Variant is_arrow : type -> Prop :=
  Is_Arrow τ σ : is_arrow (τ → σ).

(** Without [dependent induction], still needs axiom [Streicher K]. *)
Lemma canonical_forms' : forall Γ τ (t : (Γ ⊢ τ)%term),
    zilch Γ -> is_arrow τ ->
    (forall t', ~ (t -->  t')) -> value t.
Proof.
  intros Γ τ t HΓ Hτ H;
    induction t as [Γ n τ Hn | Γ τ ρ t IHt | Γ τ ρ t₁ IHt₁ t₂ _]; eauto.
  - inv HΓ; inv Hτ; exfalso; clear H.
    rewrite nth_error_nil in Hn.
    discriminate.
  - exfalso.
    pose proof IHt₁ HΓ (Is_Arrow _ _) as IH; clear IHt₁.
    assert (Ht₁ : forall t₁', ~ (t₁ -->  t₁')).
    { intros t₁' Ht₁.
      specialize H with (t':= (t₁' ⋅ t₂)%term); eauto. }
    apply IH in Ht₁; clear IH; inv Ht₁.
    (*Print Assumptions Eqdep.EqdepTheory.inj_pair2.*)
    apply Eqdep.EqdepTheory.inj_pair2 in H3; subst.
    specialize H with (t [[ t₂ ]])%term; auto.
Qed.

(* Print Assumptions canonical_forms'. *)

Lemma canonical_forms : forall τ σ (t : ([] ⊢ τ → σ)%term),
      (forall t', ~ (t -->  t')) ->
    exists body, t = (`λ body)%term.
Proof.
  intros τ σ t H.
  pose proof canonical_forms'
       [] _ t zilch_nil (Is_Arrow _ _) H as H'; clear H; inv H'.
  apply Eqdep.EqdepTheory.inj_pair2 in H; subst; eauto.
Qed.

(* Print Assumptions canonical_forms. *)
