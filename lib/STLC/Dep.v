From Lambda Require Export Util.Lists STLC.SimpleTypes.

(** * Simply Typed Lambda Calculus. *)

(** Inspired by
    Programming Language Foundations in Agda. *)

(** De Bruijn syntax. *)

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term : list type -> type -> Set :=
| Id (Γ : list type) (n : nat) (τ : type) :
    nth_error Γ n = Some τ ->
    Γ ⊢ τ
| Abs (Γ : list type) (τ τ' : type) :
    τ :: Γ ⊢ τ' ->
    Γ ⊢ τ → τ'
| App (Γ : list type) (τ τ' : type) :
    Γ ⊢ τ → τ' ->
    Γ ⊢ τ ->
    Γ ⊢ τ'
where "Γ '⊢' τ" := (term Γ τ) : type_scope.

Equations Derive Signature NoConfusion NoConfusionHom Subterm for term.

Local Hint Constructors term : core.

Definition term_of_id :
  forall {Γ : list type} (n : nat) (H : n < length Γ),
    Γ ⊢ lookup H := ltac:(eauto using nth_error_lookup).

Definition term_of_nth_error
           {Γ τ} (H : {n | nth_error Γ n = Some τ}) : Γ ⊢ τ :=
  match H with
  | exist _ _ Hn => Id _ _ _ Hn
  end.

Definition App_eq
           (Γ : list type) (τ ρ σ : type)
           (t₁ : Γ ⊢ τ → ρ) (t₂ : Γ ⊢ σ)
  : τ = σ -> Γ ⊢ ρ.
Proof.
  intros H; subst; exact (App _ _ _ t₁ t₂).
Defined.

Local Hint Resolve App_eq : core.

Definition App_lookup
           (Γ : list type) (n : nat) (H : n < length Γ) (τ ρ : type)
           (t₁ : Γ ⊢ lookup H) (t₂ : Γ ⊢ τ) :
  lookup H = τ → ρ -> Γ ⊢ ρ.
Proof.
  intros Heq; rewrite Heq in t₁; eauto using App.
Defined.

Local Hint Resolve App_lookup : core.

Declare Scope term_scope.
Delimit Scope term_scope with term.

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

Equations
  Rename
  {Γ Δ} :
  (forall τ, {n | nth_error Γ n = Some τ} ->
        {k | nth_error Δ k = Some τ}) -> forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
      Rename f (Id _ _ _ Hm)   := term_of_nth_error (f _ (exist _ _ Hm));
      Rename f (λ ρ ⇒ t')%term := (`λ Rename (ext_nth_error f ρ) t')%term;
      Rename f (t₁ ⋅ t₂)%term  := (Rename f t₁ ⋅ Rename f t₂)%term.

Equations exts_has : forall {Γ Δ},
    (forall {τ}, Has τ Γ -> Δ ⊢ τ) ->
    forall {ρ σ}, Has σ (ρ :: Γ) -> ρ :: Δ ⊢ σ :=
  exts_has f HasO := Id _ 0 _ _;
  exts_has f (HasS hs) :=
    Rename (fun τ '(exist _ n hn) => exist _ (S n) _) (f _ hs).

Definition exts : forall {Γ Δ},
    (forall τ, {n | nth_error Γ n = Some τ} -> Δ ⊢ τ) ->
    forall ρ σ, {k | nth_error (ρ :: Γ) k = Some σ} -> ρ :: Δ ⊢ σ.
Proof.
  intros Γ Δ f ρ σ H.
  apply nth_error_Has' in H.
  pose proof (fun t H => f t (Has_nth_error H)) as f'.
  exact (exts_has f' H).
Defined.

Equations
  subs : forall {Γ Δ},
    (forall τ, {n | nth_error Γ n = Some τ} -> Δ ⊢ τ) ->
    forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
  subs f (Id _ _ _ Hn)   := f _ (exist _ _ Hn);
  subs f (λ ρ ⇒ t')%term := (`λ subs (exts f ρ) t')%term;
  subs f (t₁ ⋅ t₂)%term  := (subs f t₁ ⋅ subs f t₂)%term.

Definition sub
           {Γ τ σ}
           (body : τ :: Γ ⊢ σ) (arg : Γ ⊢ τ) : Γ ⊢ σ.
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

Inductive bred {Γ} : forall {τ}, Γ ⊢ τ -> Γ ⊢ τ -> Prop :=
| bred_bred τ τ' (t₁ : τ :: Γ ⊢ τ') t₂ :
    ((`λ t₁) ⋅ t₂)%term --> (t₁ [[ t₂ ]])%term
| bred_abs τ τ' (t t' : τ :: Γ ⊢ τ') :
    t -->  t' ->
    (`λ t)%term --> (`λ t')%term
| bred_app_l τ τ' (t₁ t₁' : Γ ⊢ τ → τ') t₂ :
    t₁ -->  t₁' ->
    (t₁ ⋅ t₂)%term -->  (t₁' ⋅ t₂)%term
| bred_app_r τ τ' (t₁ : Γ ⊢ τ → τ') t₂ t₂' :
    t₂ -->  t₂' ->
    (t₁ ⋅ t₂)%term -->  (t₁ ⋅ t₂')%term
where "x '-->' y" := (bred x y) : type_scope.

Variant value {Γ} : forall {τ}, Γ ⊢ τ -> Prop :=
  Abs_value τ τ' (t : τ :: Γ ⊢ τ') : value (`λ t)%term.
Derive Signature for value.

Lemma canonical_forms_abs : forall {τ τ'} (t : [] ⊢ τ → τ'),
    value t -> exists body : [τ] ⊢ τ', t = (`λ body)%term.
Proof.
  intros τ τ' t v; depelim v; eauto.
Qed.

Print Assumptions canonical_forms_abs.

Local Hint Constructors value : core.
Local Hint Constructors bred : core.

Theorem Progress : forall τ (t : [] ⊢ τ),
    value t \/ exists t', t --> t'.
Proof.
  intros τ t; depind t; cbn in *; try discriminate; eauto.
  - exfalso; rewrite nth_error_nil in e; discriminate.
  - clear IHt2. destruct IHt1 as [v1 | (t1' & ih1)]; eauto.
    apply canonical_forms_abs in v1 as [t1' ?]; subst; eauto.
Qed.

Print Assumptions Progress.
