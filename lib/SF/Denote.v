Require Export Lambda.SF.Dep.
Require Coq.Vectors.Vector.
Import Vector.VectorNotations.

Equations denote_type : forall {Δ : nat}, Vector.t Set Δ  -> type Δ -> Type :=
  denote_type σ (TId X)  := Vector.nth σ X;
  denote_type σ (∀ τ)%ty := forall (X : Set), denote_type (X :: σ)%vector τ;
  denote_type σ (τ₁ → τ₂)%ty :=
    denote_type σ τ₁ -> denote_type σ τ₂.

Fail Equations denote_term
  : forall {Δ : nat} {Γ : list (type Δ)}
      {τ : type Δ} (σ : Vector.t Set Δ),
    hlist (denote_type σ) Γ -> Γ ⊢ τ -> denote_type σ τ :=
  denote_term _ ϵ (Id _ _ hs) := lookup_has ϵ hs;
  denote_term σ ϵ (λ τ ⇒ t)%term :=
    fun x : denote_type σ τ => denote_term σ (hcons x ϵ) t;
  denote_term σ ϵ (t₁ ⋅ t₂)%term :=
    (denote_term σ ϵ t₁) (denote_term σ ϵ t₂);
  denote_term (Δ:=Δ) (Γ:=Γ) σ ϵ (Λ t)%term :=
    fun (X : Set) => denote_term (X :: σ) ϵ t;
  denote_term σ ϵ (t ⦗τ⦘)%term :=
    (denote_term σ ϵ t) (denote_type σ ϵ τ).
