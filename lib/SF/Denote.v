Require Export Lambda.SF.Dep.
Require Coq.Vectors.Vector.
Import Vector.VectorNotations.

(** [Prop] is used instead of [Set] & [Type]
    because [Prop], like System F, is impredicative. *)

Equations eq_doh : forall {A B : Type}, A = B -> A -> B :=
  eq_doh eq_refl a := a.

Equations denote_type : forall {Δ : nat}, Vector.t Prop Δ  -> type Δ -> Prop :=
  denote_type σ (TId X)  := Vector.nth σ X;
  denote_type σ (∀ τ)%ty := forall (X : Prop), denote_type (X :: σ)%vector τ;
  denote_type σ (τ₁ → τ₂)%ty :=
    denote_type σ τ₁ -> denote_type σ τ₂.

(*Local Transparent denote_type.*)

Definition denote_type_cons :
  forall {Δ : nat} {τ : type Δ} {σ : Vector.t Prop Δ} (X : Prop),
    denote_type σ τ -> denote_type (X :: σ)%vector (rename_type Fin.FS τ).
Proof.
  (* TODO: needs mapply lemma. *)
Admitted.

Equations denote_hlist_cons :
  forall {Δ : nat} {Γ : list (type Δ)} {σ : Vector.t Prop Δ} (X : Prop),
    hlist (denote_type σ) Γ ->
    hlist (denote_type (X :: σ)%vector) (map (rename_type Fin.FS) Γ) :=
  denote_hlist_cons _ hnil := hnil;
  denote_hlist_cons X (hcons τ hl) :=
    hcons (denote_type_cons X τ) (denote_hlist_cons X hl).

Lemma denote_type_sub :
  forall {Δ : nat} (σ : Vector.t Prop Δ) (τ : type (S Δ)) (τ' : type Δ),
    denote_type σ (τ `[[τ']])%ty
    = (denote_type (denote_type σ τ' :: σ)%vector τ).
Proof.
  intros Δ σ τ τ'.
  unfold "_ `[[ _ ]]".
Admitted.

Equations denote_term
  : forall {Δ : nat} {Γ : list (type Δ)}
      {τ : type Δ} (σ : Vector.t Prop Δ),
    hlist (denote_type σ) Γ -> Γ ⊢ τ -> denote_type σ τ :=
  denote_term _ ϵ (Id _ _ hs) := lookup_has ϵ hs;
  denote_term σ ϵ (λ τ ⇒ t)%term :=
    fun x : denote_type σ τ => denote_term σ (hcons x ϵ) t;
  denote_term σ ϵ (t₁ ⋅ t₂)%term :=
    (denote_term σ ϵ t₁) (denote_term σ ϵ t₂);
  denote_term (Δ:=Δ) (Γ:=Γ) σ ϵ (Λ t)%term :=
    fun (X : Prop) => denote_term (X :: σ) (denote_hlist_cons X ϵ) t;
  denote_term (Δ:=Δ) (Γ:=Γ) σ ϵ (t ⦗τ⦘)%term := _.
Next Obligation.
Proof.
  rewrite denote_type_sub.
  exact (denote_term _ _ _ σ ϵ t (denote_type σ τ)).
Defined.
