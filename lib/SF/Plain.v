Require Export Lambda.Util.
From Equations Require Export Equations.

(** * System F. *)

(** De Bruijn syntax. *)

Inductive typ : Set :=
| TId (X : nat)
| TForall (τ : typ)
| TArrow (τ₁ τ₂ : typ).

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Coercion TId : nat >-> typ.
Notation "'∀' x"
  := (TForall x) (at level 20, right associativity) : typ_scope.
Notation "x '→' y"
  := (TArrow x y) (at level 19, right associativity) : typ_scope.

Equations typ_eq_dec : forall (τ ρ : typ), {τ = ρ} + {τ <> ρ} :=
  typ_eq_dec (TId n) (TId m)
    with PeanoNat.Nat.eq_dec n m => {
    | left  _ => left  _
    | right _ => right _ };
  typ_eq_dec (∀ τ)%typ (∀ ρ)%typ
    with typ_eq_dec τ ρ => {
    | left  _ => left  _
    | right _ => right _ };
  typ_eq_dec (τ → τ')%typ (ρ → ρ')%typ
    with typ_eq_dec τ ρ => {
    | right _ => right _
    | left  _ with typ_eq_dec τ' ρ' => {
      | right _ => right _
      | left  _ => left  _}};
  typ_eq_dec _ _ := right _.

Definition ext (ρ : nat -> nat) (X : nat) : nat :=
  match X with
  | O   => O
  | S n => S (ρ n)
  end.

Fixpoint rename_typ (ρ : nat -> nat) (τ : typ) : typ :=
  match τ with
  | TId X        =>  ρ X
  | (∀ τ)%typ    => (∀ rename_typ (ext ρ) τ)%typ
  | (τ → τ')%typ => (rename_typ ρ τ → rename_typ ρ τ')%typ
  end.

Definition exts_typ (σ : nat -> typ) (X : nat) : typ :=
  match X with
  | O   => O
  | S n => rename_typ S (σ n)
  end.

Fixpoint subs_typ (σ : nat -> typ) (τ : typ) : typ :=
  match τ with
  | TId X        => σ X
  | (∀ τ)%typ    => (∀ subs_typ (exts_typ σ) τ)%typ
  | (τ → τ')%typ => (subs_typ σ τ → subs_typ σ τ')%typ
  end.

Definition sub_typ_helper (τ : typ) (X : nat) : typ :=
  match X with
  | O   => τ
  | S n => n
  end.

Definition sub_typ (body arg : typ) : typ :=
  subs_typ (sub_typ_helper arg) body.

Notation "x '`[[' y ']]'"
  := (sub_typ x y) (at level 12, left associativity) : typ_scope.

Reserved Notation "x '⊢ok' y" (at level 80, no associativity).

Inductive ok_typ (Δ : nat) : typ -> Prop :=
| ok_TId X :
  X < Δ ->
  Δ ⊢ok X
| ok_TForall τ :
  S Δ ⊢ok τ ->
  Δ ⊢ok (∀ τ)%typ
| ok_TArrow τ₁ τ₂ :
  Δ ⊢ok τ₁ ->
  Δ ⊢ok τ₂ ->
  Δ ⊢ok (τ₁ → τ₂)%typ
where "x '⊢ok' y" := (ok_typ x y) : type_scope.

Local Hint Constructors ok_typ : core.

Lemma ext_ok : forall (ρ : nat -> nat) (Δ₁ Δ₂ X : nat),
    (forall Y, Y < Δ₁ -> ρ Y < Δ₂) ->
    X < S Δ₁ -> ext ρ X < S Δ₂.
Proof.
  intros ρ Δ₁ Δ₂ [| n] h1 h2; cbn; try lia.
  apply Lt.lt_S_n,h1 in h2; lia.
Qed.

Local Hint Resolve ext_ok : core.

Lemma rename_typ_ok : forall (τ : typ) (ρ : nat -> nat) (Δ₁ Δ₂ : nat),
    (forall Y, Y < Δ₁ -> ρ Y < Δ₂) ->
    Δ₁ ⊢ok τ -> Δ₂ ⊢ok rename_typ ρ τ.
Proof.
  intros τ  ρ Δ₁ Δ₂ hρ h.
  generalize dependent ρ;
    generalize dependent Δ₂.
  induction h as [Δ₁ X hX | Δ₁ τ hτ ihτ | Δ₁ τ₁ τ₂ hτ₁ ihτ₁ hτ₂ ihτ₂];
    intros Δ₂ ρ hρ; cbn; eauto.
Qed.

Local Hint Resolve rename_typ_ok : core.

Lemma exts_typ_ok : forall (Δ₁ Δ₂ X : nat) (σ : nat -> typ),
    (forall Y, Y < Δ₁ -> Δ₂ ⊢ok σ Y) ->
    X < S Δ₁ -> S Δ₂ ⊢ok exts_typ σ X.
Proof.
  intros Δ₁ Δ₂ [| X] σ hσ h; cbn.
  - constructor; lia.
  - apply Lt.lt_S_n,hσ,
      rename_typ_ok with (ρ:=S) (Δ₂:=S Δ₂) in h;
      assumption || lia.
Qed.

Local Hint Resolve exts_typ_ok : core.

Lemma subs_typ_ok : forall (Δ₁ Δ₂ : nat) (τ : typ) (σ : nat -> typ),
    (forall Y, Y < Δ₁ -> Δ₂ ⊢ok σ Y) ->
    Δ₁ ⊢ok τ -> Δ₂ ⊢ok (subs_typ σ τ).
Proof.
  intros Δ₁ Δ₂ τ σ hσ h;
    generalize dependent σ;
    generalize dependent Δ₂.
  induction h as [Δ₁ X hX | Δ₁ τ hτ ihτ | Δ₁ τ₁ τ₂ hτ₁ ihτ₁ hτ₂ ihτ₂];
    intros Δ₂ σ hσ; cbn; eauto.
Qed.

Local Hint Resolve subs_typ_ok : core.

Lemma sub_typ_helper_ok : forall (Δ : nat) (τ : typ),
    Δ ⊢ok τ -> forall Y : nat, Y < S Δ -> Δ ⊢ok sub_typ_helper τ Y.
Proof.
  intros Δ τ h [| Y] hY; cbn; assumption || constructor; lia.
Qed.

Local Hint Resolve sub_typ_helper_ok : core.

Lemma sub_typ_ok : forall (Δ : nat) (τ τ' : typ),
    S Δ ⊢ok τ -> Δ ⊢ok τ' -> Δ ⊢ok (τ `[[ τ' ]])%typ.
Proof.
  intros Δ τ τ' h h'; unfold "_ `[[ _ ]]"; eauto.
Qed.

Local Hint Resolve sub_typ_ok : core.

Inductive trm : Set :=
| Id (x : nat)
| Abs (τ : typ) (t : trm)
| App (t₁ t₂ : trm)
| TypAbs (t : trm)
| TypApp (t : trm) (τ : typ).

Declare Scope trm_scope.
Delimit Scope trm_scope with trm.
Coercion Id : nat >-> trm.
Notation "'λ' τ '⇒' t"
  := (Abs τ t)
       (at level 41, right associativity) : trm_scope.
Notation "'λ' τ '↣' .. '↣' ρ '⇒' t"
  := (Abs τ .. (Abs ρ t) ..)
       (at level 41, right associativity) : trm_scope.
Notation "x '⋅' y"
  := (App x y)
       (at level 40, left associativity) : trm_scope.
Notation "'Λ' x"
  := (TypAbs x)
       (at level 43, right associativity) : trm_scope.
Notation "t '⦗' τ '⦘'"
  := (TypApp t τ)
       (at level 39, left associativity) : trm_scope.

Reserved Notation "x ⊢ y ∈ z" (at level 80, no associativity).

Inductive trm_typ (Δ : nat) (Γ : list typ) : trm -> typ -> Prop :=
| Id_typ x τ :
  nth_error Γ x = Some τ ->
  (Δ,Γ) ⊢ x ∈ τ
| Abs_typ τ τ' t :
  Δ ⊢ok τ ->
  (Δ,τ::Γ) ⊢  t            ∈ τ' ->
  (Δ,  Γ) ⊢ (λ τ ⇒ t)%trm ∈ (τ → τ')%typ
| App_typ τ τ' t₁ t₂ :
  (Δ,Γ) ⊢  t₁           ∈ (τ → τ')%typ ->
  (Δ,Γ) ⊢  t₂           ∈  τ ->
  (Δ,Γ) ⊢ (t₁ ⋅ t₂)%trm ∈  τ'
| TypAbs_typ τ t :
  (S Δ, map (rename_typ S) Γ) ⊢    t      ∈    τ ->
  (  Δ,                    Γ) ⊢ (Λ t)%trm ∈ (∀ τ)%typ
| TypApp_typ τ τ' t :
  Δ ⊢ok τ' ->
  (Δ,Γ) ⊢  t           ∈ (∀ τ)%typ ->
  (Δ,Γ) ⊢ (t ⦗τ'⦘)%trm ∈ (τ `[[τ']])%typ
where "x ⊢ y ∈ z" := (trm_typ (fst x) (snd x) y z) : type_scope.

Local Hint Constructors trm_typ : core.

Local Hint Unfold fst : core.
Local Hint Unfold snd : core.

Lemma trm_typ_ok : forall Δ Γ t τ,
    (Δ,Γ) ⊢ t ∈ τ ->
    Forall (ok_typ Δ) Γ ->
    Δ ⊢ok τ.
Proof.
  intros Δ Γ t τ h hΓ; cbn in *.
  induction h as
    [ Δ Γ X τ hX
    | Δ Γ τ t hok h ih
    | Δ Γ τ τ' t₁ t₂ h₁ ih₁ h₂ ih₂
    | Δ Γ τ t h ih
    | Δ Γ τ τ' t hok h ih ]; cbn in *; eauto.
  - rewrite Forall_forall in hΓ.
    eauto using nth_error_In.
  - pose proof ih₁ hΓ as ih; inv ih; assumption.
  - constructor. apply ih.
    clear dependent t; clear dependent τ.
    rewrite Forall_forall in *.
    intros rτ h.
    rewrite in_map_iff in h.
    destruct h as (τ & ? & inτ); subst.
    apply rename_typ_ok with (Δ₁:=Δ); lia || auto.
  - apply ih in hΓ; inv hΓ; auto.
Qed.

Fixpoint rename_trm (ρ : nat -> nat) (t : trm) : trm :=
  match t with
  | Id x          => ρ x
  | (λ τ ⇒ t)%trm => (λ τ ⇒ rename_trm (ext ρ) t)%trm
  | (t₁ ⋅ t₂)%trm => (rename_trm ρ t₁ ⋅ rename_trm ρ t₂)%trm
  | (Λ t)%trm     => (Λ rename_trm ρ t)%trm
  | (t ⦗τ⦘)%trm   => (rename_trm ρ t ⦗τ⦘)%trm
  end.

Definition exts_trm (σ : nat -> trm) (x : nat) : trm :=
  match x with
  | O   => O
  | S n => rename_trm S (σ n)
  end.

Fail Fixpoint subs_trm (σ : nat -> trm) (t : trm) : trm :=
  match t with
  | Id x          => σ x
  | (λ τ ⇒ t)%trm => (λ τ ⇒ subs_trm (exts_trm σ) t)%trm
  | (t₁ ⋅ t₂)%trm => (subs_trm σ t₁ ⋅ subs_trm σ t₂)%trm
  | (Λ t)%trm     => (Λ _)%trm (* TODO *)
  | (t ⦗τ⦘)%trm   => (subs_trm σ t ⦗τ⦘)%trm
  end.
