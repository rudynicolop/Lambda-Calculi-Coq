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

Derive Signature for term.
Equations Derive NoConfusion NoConfusionHom Subterm for term.

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
