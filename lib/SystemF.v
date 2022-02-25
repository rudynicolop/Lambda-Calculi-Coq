Require Export Lambda.Util.
From Equations Require Export Equations.

(** * System F *)

Reserved Notation "x '≤' y" (at level 80, no associativity).

Inductive LE (n : nat) : nat -> Set :=
| LE_n : n ≤ n
| LE_S m :
  n ≤ m ->
  n ≤ S m
where "x ≤ y" := (LE x y) : type_scope.

Derive Signature for LE.
Equations Derive NoConfusion NoConfusionHom Subterm for LE.

Equations S_LE : forall {n m}, n ≤ m -> S n ≤ S m :=
  S_LE (LE_n n) := LE_n (S n);
  S_LE (LE_S _ _ hnm) := LE_S _ _ (S_LE hnm).

Equations ext_LE : forall {Δ₁ Δ₂ : nat},
    (forall n, n ≤ Δ₁ -> n ≤ Δ₂) -> forall {n : nat}, n ≤ S Δ₁ -> n ≤ S Δ₂ :=
  ext_LE ρ (LE_n _)     := S_LE (ρ _ (LE_n _));
  ext_LE ρ (LE_S _ _ h) := LE_S _ _ (ρ _ h).

Definition LT (n m : nat) : Set := S n ≤ m.
Notation "x '`<' y"
  := (LT x y) (at level 80, no associativity) : type_scope.

Definition S_LT {n m : nat} : n `< m -> S n `< S m := S_LE.

Equations LT_LE : forall {n m : nat}, n `< m -> n ≤ m :=
  LT_LE (LE_n _)     := LE_S _ _ (LE_n _);
  LT_LE (LE_S _ _ h) := LE_S _ _ (LT_LE h).

Lemma whyme : forall m n : nat,
    (forall r, r <= m -> r <= n) -> m <= n.
Proof.
  intros m n h.
  apply h. constructor.
Qed.

Equations LE_0_l : forall n : nat, 0 ≤ n :=
  LE_0_l 0     := LE_n _;
  LE_0_l (S n) := LE_S _ _ (LE_0_l n).

Print whyme.

Definition bruh (n m : nat) (ρ : forall r, r ≤ m -> r ≤ n) : m ≤ n := ρ m (LE_n m).

Lemma helpme : forall m n : nat,
    (forall r, r < m -> r < n) -> m <= n.
Proof.
  intros m n h.
  unfold "<" in *.
  destruct m as [| m].
  - apply PeanoNat.Nat.le_0_l.
  - apply h. constructor.
Qed.

Print helpme.

Equations bruh' : forall (m n : nat), (forall r, r `< m -> r `< n) -> m ≤ n :=
  bruh' 0     n _ := LE_0_l n;
  bruh' (S m) n ρ := ρ m (LE_n (S m)).

Lemma ext_lt : forall (m n s : nat),
    (forall r, r < m -> r < n) -> s < S m -> s < S n.
Proof.
  intros m n s Q h.
  unfold "<" in *.
  inversion h; subst.
  - clear h. apply le_n_S.
    auto using helpme.
  - constructor. apply Q,H0.
Qed.

Print ext_lt.

Definition ext_LT {Δ₁ Δ₂ : nat} (ρ : forall n, n `< Δ₁ -> n `< Δ₂)
  : forall n, n `< S Δ₁ -> n `< S Δ₂.
Proof.
  unfold "`<" in *.
  intros n h. inversion h; subst.
  - clear h.
    apply S_LE.
    auto using bruh'.
  - constructor.
    apply ρ, H0.
Defined.

Inductive type (Δ : nat) : Set :=
| TId n : n `< Δ -> type Δ
| TForall (τ : type (S Δ)) : type Δ
| TArrow (τ₁ τ₂ : type Δ) : type Δ.

Arguments TId {_}.
Arguments TForall {_}.
Arguments TArrow {_}.

Derive Signature for type.
Equations Derive NoConfusion NoConfusionHom Subterm for type.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.

Notation "'∀' x"
  := (TForall x) (at level 20, right associativity) : ty_scope.
Notation "x → y"
  := (TArrow x y) (at level 19, right associativity) : ty_scope.

Equations S_type : forall {Δ : nat}, type Δ -> type (S Δ) :=
  S_type (TId n h)    := TId (S n) (S_LT h);
  S_type (∀ τ)%ty     := (∀ S_type τ)%ty;
  S_type (τ₁ → τ₂)%ty := (S_type τ₁ → S_type τ₂)%ty.

Equations rename_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> n `< Δ₂) -> type Δ₁ -> type Δ₂ :=
  rename_type ρ (TId _ h)    := TId _ (ρ _ h);
  rename_type ρ (∀ τ)%ty     := (∀ rename_type (ext_LT ρ) τ)%ty;
  rename_type ρ (τ₁ → τ₂)%ty := (rename_type ρ τ₁ → rename_type ρ τ₂)%ty.

Definition exts_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> type Δ₂) -> n `< S Δ₁ -> type (S Δ₂).

Equations subs_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> type Δ₂) -> type Δ₁ -> type Δ₂.

Definition sub_type : forall {Δ : nat}, type (S Δ) -> type Δ -> type Δ.

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term {Δ : nat} (Γ : list (type Δ)) : type Δ -> Set :=
| Id (τ : type Δ) :
  Has τ Γ ->
  Γ ⊢ τ
| Abs (τ τ' : type Δ) :
  τ :: Γ ⊢ τ' ->
  Γ ⊢ (τ → τ')%ty
| App (τ τ' : type Δ) :
  Γ ⊢ (τ → τ')%ty ->
  Γ ⊢ τ ->
  Γ ⊢ τ'
| TypAbs (τ : type (S Δ)) :
  map S_type Γ ⊢ τ ->
  Γ ⊢ (∀ τ)%ty
| TypApp (τ : type (S Δ)) (τ' : type Δ) :
  Γ ⊢ (∀ τ)%ty ->
  Γ ⊢ τ `[[ τ' ]]
where "Γ '⊢' τ" := (term Γ τ).

Derive Signature for term.
Equations Derive NoConfusion NoConfusionHom Subterm for term.
