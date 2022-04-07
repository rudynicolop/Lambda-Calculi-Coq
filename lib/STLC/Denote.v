Require Export Lambda.STLC.Has.

Reserved Notation "'`⟦' τ '⟧'"
         (at level 20, no associativity).

Fixpoint denote_type (τ : type) : Set :=
  match τ with
  | ⊥%ty => Empty_set
  | (τ₁ → τ₂)%ty => (`⟦τ₁⟧ -> `⟦τ₂⟧)%ty
  end
where "'`⟦' τ '⟧'" := (denote_type τ) : ty_scope.

(*Reserved Notation "'⟦' t '⟧'"
         (at level 20, no associativity).*)

Equations denote_term : forall {Γ : list type} {τ : type},
    hlist denote_type Γ -> Γ ⊢ τ -> `⟦ τ ⟧ :=
  denote_term ϵ (Id _ _ hs)    := lookup_has ϵ hs;
  denote_term ϵ (λ τ ⇒ t)%term := fun x : `⟦ τ ⟧ => denote_term (hcons x ϵ) t;
  denote_term ϵ (t₁ ⋅ t₂)%term := (denote_term ϵ t₁) (denote_term ϵ t₂)
(*where "⟦ t ⟧" := (denote_term t) : term_scope*).
