From Lambda Require Export ListUtil STLC.SimpleTypes.

(** Inspired by
    Programming Language Foundations in Agda. *)

(** De Bruijn syntax. *)

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term : list type -> type -> Set :=
| Id (Γ : list type) (τ : type) :
  Has τ Γ ->
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

Declare Scope term_scope.
Delimit Scope term_scope with term.

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

Equations
  Rename
  {Γ Δ} :
  (forall {τ}, Has τ Γ -> Has τ Δ) -> forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
  Rename f (Id _ _ h)   := Id _ _ (f _ h);
  Rename f (λ ρ ⇒ t')%term := (`λ Rename (@ext_has _ _ _ f ρ) t')%term;
  Rename f (t₁ ⋅ t₂)%term  := (Rename f t₁ ⋅ Rename f t₂)%term.

Equations Exts : forall {Γ Δ},
    (forall {τ}, Has τ Γ -> Δ ⊢ τ) ->
    forall ρ {σ}, Has σ (ρ :: Γ) -> ρ :: Δ ⊢ σ :=
  Exts f _ HasO := Id _ _ HasO;
  Exts f _ (HasS hs) := Rename (fun τ => @HasS _ τ _ _) (f _ hs).

Equations
  subs : forall {Γ Δ},
    (forall {τ}, Has τ Γ -> Δ ⊢ τ) ->
    forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
  subs f (Id _ _ h)   := f _ h;
  subs f (λ ρ ⇒ t')%term := (`λ subs (fun τ => Exts f ρ (σ:=τ)) t')%term;
  subs f (t₁ ⋅ t₂)%term  := (subs f t₁ ⋅ subs f t₂)%term.

Equations sub_helper : forall {Γ τ}, Γ ⊢ τ -> forall τ', Has τ' (τ :: Γ) -> Γ ⊢ τ' :=
  sub_helper t _ HasO := t;
  sub_helper _ _ (HasS hs) := Id _ _ hs.

Definition sub {Γ τ τ'} (body : τ :: Γ ⊢ τ') (arg : Γ ⊢ τ) : Γ ⊢ τ' :=
    subs (sub_helper arg) body.

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

Print Assumptions bred.

Local Hint Constructors bred : core.

Variant value {Γ : list type} : forall {τ : type}, Γ ⊢ τ -> Prop :=
  Abs_value (τ τ' : type) (t : τ :: Γ ⊢ τ') : value (`λ t)%term.
Derive Signature for value.

Print Assumptions value.

Lemma canonical_forms_abs : forall {τ τ' : type} (t : [] ⊢ (τ → τ')%ty),
    value t -> exists body : [τ] ⊢ τ', t = (`λ body)%term.
Proof.
  intros τ τ' t v.
  depelim v; eauto.
Qed.

Print Assumptions canonical_forms_abs.

Local Hint Constructors bred : core.
Local Hint Constructors value : core.

Lemma Progress : forall {τ} (t : [] ⊢ τ), value t \/ exists t', t --> t'.
Proof.
  intros τ t; depind t; eauto.
  - inv h.
  - clear IHt2.
    destruct IHt1 as [v1 | (t1' & ih1)]; eauto.
    apply canonical_forms_abs in v1 as [t1' ?]; subst; eauto.
Qed.

Print Assumptions Progress.
