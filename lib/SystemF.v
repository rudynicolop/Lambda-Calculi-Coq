Require Export Lambda.Util.
From Equations Require Export Equations.
Require Coq.Vectors.Fin.
Module FIN.
  Export Coq.Vectors.Fin.

  Derive Signature for t.
  Equations Derive NoConfusion NoConfusionHom Subterm for t.
End FIN.

(** * System F *)

Inductive type (Δ : nat) : Set :=
| TId : Fin.t Δ -> type Δ
| TForall (τ : type (S Δ)) : type Δ
| TArrow (τ₁ τ₂ : type Δ) : type Δ.

Arguments TId {_}.
Arguments TForall {_}.
Arguments TArrow {_}.

Derive Signature for type.
Equations Derive NoConfusion NoConfusionHom Subterm for type.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Coercion TId : Fin.t >-> type.
Notation "'∀' x"
  := (TForall x) (at level 20, right associativity) : ty_scope.
Notation "x → y"
  := (TArrow x y) (at level 19, right associativity) : ty_scope.

Equations upshift_type : forall {Δ : nat} (n : nat), type Δ -> type (n + Δ) :=
  upshift_type n (TId m) := Fin.R n m;
  upshift_type n (∀ τ)%ty := (∀ eq_rect _ _ (upshift_type n τ)%ty _ _)%ty;
  upshift_type n (τ₁ → τ₂)%ty := (upshift_type n τ₁ → upshift_type n τ₂)%ty.

Notation "'↑'" := upshift_type (at level 0, no associativity) : ty_scope.

Equations S_type : forall {Δ : nat}, type Δ -> type (S Δ) :=
  S_type (TId n)      := Fin.FS n;
  S_type (∀ τ)%ty     := (∀ S_type τ)%ty;
  S_type (τ₁ → τ₂)%ty := (S_type τ₁ → S_type τ₂)%ty.

Equations mapply : forall {F : nat -> Set} (m : nat),
    (forall {n : nat}, F n -> F (S n)) -> forall {n : nat}, F n -> F (m + n) :=
  mapply 0 f a := a;
  mapply (S n) f a := f _ (mapply n f a).

Notation "f '`^' m" := (mapply m f) (at level 10, left associativity).

Lemma mapply_R : forall (n m : nat) (f : Fin.t n),
    Fin.R m f = @Fin.FS `^ m f.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m ih]; intros n f; simpl.
  - rewrite mapply_equation_1. reflexivity.
  - rewrite mapply_equation_2, ih. reflexivity.
Defined.

Lemma upshift_type_0 : forall {Δ : nat} (τ : type Δ), ↑%ty 0 τ = τ.
Proof.
  intros Δ τ. funelim (↑%ty 0 τ).
  - rewrite upshift_type_equation_1. reflexivity.
  - rewrite upshift_type_equation_2; cbn.
    unfold upshift_type_obligations_obligation_1, eq_sym.
    pose proof Peano_dec.UIP_nat _ _ (plus_n_Sm 0 Δ) as h.
    cbn in h; specialize h with eq_refl.
    rewrite h, H; clear h H. reflexivity.
  - rewrite upshift_type_equation_3, H, H0. reflexivity.
Defined.

Lemma upshift_type_S_type : forall {Δ : nat} (n : nat) (τ : type Δ),
    (↑ n τ)%ty = @S_type `^ n τ.
Proof.
  intros Δ n τ. funelim (↑%ty n τ).
  - rewrite upshift_type_equation_1,mapply_R.
    funelim (@Fin.FS `^ n m).
    + do 2 rewrite mapply_equation_1; reflexivity.
    + do 2 rewrite mapply_equation_2.
      rewrite <- H. reflexivity.
  - rewrite upshift_type_equation_2, H; clear H.
    unfold upshift_type_obligations_obligation_1.
    funelim (@S_type `^ n τ).
    + do 2 rewrite mapply_equation_1.
      unfold eq_sym.
      pose proof Peano_dec.UIP_nat _ _ (plus_n_Sm 0 Δ) as h.
      cbn in h; specialize h with eq_refl.
      rewrite h. reflexivity.
    + do 2 rewrite mapply_equation_2.
      rewrite <- H, S_type_equation_2; f_equal.
      rewrite <- map_subst_map.
      f_equal; apply Peano_dec.UIP_nat.
  - rewrite upshift_type_equation_3, H, H0; clear H H0.
    funelim (@S_type `^ n (τ₁ → τ₂)%ty).
    + do 3 rewrite mapply_equation_1. reflexivity.
    + do 3 rewrite mapply_equation_2.
      rewrite <- H. reflexivity.
Defined.

Equations type_eq_dec : forall {Δ : nat} (τ ρ : type Δ), {τ = ρ} + {τ <> ρ} :=
  type_eq_dec (TId n) (TId m) with Fin.eq_dec n m => {
    | left _     => left _
    | right hneq => right _ };
  type_eq_dec (∀ τ)%ty (∀ ρ)%ty with type_eq_dec τ ρ => {
    | left _     => left _
    | right hneq => right _ };
  type_eq_dec (τ → τ')%ty (ρ → ρ')%ty with type_eq_dec τ ρ => {
    | right hneq => right _
    | left _ with type_eq_dec τ' ρ' => {
      | right hneq => right _
      | left _     => left _ } };
  type_eq_dec _ _ := right _.

Equations exts_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> type Δ₂) -> Fin.t (S Δ₁) -> type (S Δ₂) :=
  exts_type σ Fin.F1     := Fin.F1;
  exts_type σ (Fin.FS n) := S_type (σ n).

Equations subs_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> type Δ₂) -> type Δ₁ -> type Δ₂ :=
  subs_type σ (TId n)     := σ n;
  subs_type σ (∀ τ)%ty    := (∀ subs_type (exts_type σ) τ)%ty;
  subs_type σ (τ → τ')%ty := (subs_type σ τ → subs_type σ τ')%ty.

Lemma S_type_subs : forall {Δ₁ Δ₂ : nat}
    (σ : Fin.t Δ₁ -> type Δ₂) (τ : type Δ₁),
    S_type (subs_type σ τ) = subs_type (exts_type σ) (S_type τ).
Proof.
  intros Δ₁ Δ₂ σ τ.
  funelim (subs_type σ τ).
  - rewrite S_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    rewrite exts_type_equation_2.
    reflexivity.
  - rewrite S_type_equation_2.
    do 2 rewrite subs_type_equation_2.
    rewrite S_type_equation_2,H. reflexivity.
  - rewrite S_type_equation_3.
    do 2 rewrite subs_type_equation_3.
    rewrite S_type_equation_3,H,H0.
    reflexivity.
Defined.

Equations sub_type_helper : forall {Δ : nat}, type Δ -> Fin.t (S Δ) -> type Δ :=
  sub_type_helper τ Fin.F1     := τ;
  sub_type_helper _ (Fin.FS n) := n.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma exts_sub_type_helper : forall {Δ : nat} (τ : type Δ),
    exts_type (sub_type_helper τ) = sub_type_helper (S_type τ).
Proof.
  intros Δ τ.
  extensionality body.
  funelim (exts_type (sub_type_helper τ) body).
  - rewrite exts_type_equation_1.
    rewrite sub_type_helper_equation_1.
    admit.
  - rewrite exts_type_equation_2.
    rewrite sub_type_helper_equation_2.
    funelim (sub_type_helper τ n).
    + rewrite sub_type_helper_equation_1.
      admit.
    + rewrite sub_type_helper_equation_2. reflexivity.
Abort.

Definition sub_type {Δ : nat} (body : type (S Δ)) (arg : type Δ) : type Δ :=
  subs_type (sub_type_helper arg) body.

Notation "x '`[[' y ']]'"
  := (sub_type x y) (at level 12, no associativity) : ty_scope.

Lemma S_type_sub : forall {Δ : nat} (τ : type (S Δ)) (τ' : type Δ),
    S_type (τ `[[ τ' ]])%ty = (S_type τ `[[ S_type τ' ]])%ty.
Proof.
  intros Δ τ τ'. unfold "_ `[[ _ ]]".
  funelim (subs_type (sub_type_helper τ') τ).
  - rewrite S_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    rewrite sub_type_helper_equation_2.
    funelim (sub_type_helper τ' n).
    + rewrite sub_type_helper_equation_1.
      admit. (* sad. *)
    + rewrite sub_type_helper_equation_2.
      reflexivity.
Abort.

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term : forall {Δ : nat}, list (type Δ) -> type Δ -> Set :=
| Id {Δ : nat} (Γ : list (type Δ)) (τ : type Δ) :
  Has τ Γ ->
  Γ ⊢ τ
| Abs {Δ : nat} (Γ : list (type Δ)) (τ τ' : type Δ) :
  τ :: Γ ⊢ τ' ->
  Γ ⊢ (τ → τ')%ty
| App {Δ : nat} (Γ : list (type Δ)) (τ τ' : type Δ) :
  Γ ⊢ (τ → τ')%ty ->
  Γ ⊢ τ ->
  Γ ⊢ τ'
| TypAbs {Δ : nat} (Γ : list (type Δ)) (τ : type (S Δ)) :
  map S_type Γ ⊢ τ ->
  Γ ⊢ (∀ τ)%ty
| TypApp {Δ : nat} (Γ : list (type Δ)) (τ : type (S Δ)) (τ' : type Δ) :
  Γ ⊢ (∀ τ)%ty ->
  Γ ⊢ (τ `[[ τ' ]])%ty
where "Γ '⊢' τ" := (term Γ τ).

Derive Signature for term.
Equations Derive NoConfusion (* NoConfusionHom *) (*Subterm*) for term.
(*Equations Derive Subterm for term.*)

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "'`λ' t"
  := (Abs _ _ _ t)
       (at level 41, right associativity) : term_scope.
Notation "'λ' τ '⇒' t"
  := (Abs _ τ _ t)
       (at level 41, right associativity) : term_scope.
Notation "'λ' τ '↣' .. '↣' ρ '⇒' t"
  := (Abs _ τ _ .. (Abs _ ρ _ t) ..)
       (at level 41, right associativity) : term_scope.
Notation "x '⋅' y"
  := (App _ _ _ x y)
       (at level 40, left associativity) : term_scope.
Notation "'Λ' x"
  := (TypAbs _ _ x)
       (at level 43, right associativity) : term_scope.
Notation "t '⦗' τ '⦘'"
  := (TypApp _ _ τ t)
       (at level 39, left associativity) : term_scope.

Definition has_map : forall {A B : Set} (f : A -> B) {l a},
    Has a l -> Has (f a) (map f l).
Proof.
  intros A B f l; induction l as [| h t ih];
    intros a H; cbn in *.
  - apply H.
  - destruct H as [H | H]; subst.
    + left; reflexivity.
    + right; apply ih,H.
Defined.

Equations S_term : forall {Δ : nat} {Γ : list (type Δ)} {τ : type Δ},
    Γ ⊢ τ -> map S_type Γ ⊢ S_type τ :=
  S_term (Id _ _ h)     := Id _ _ (has_map S_type h);
  S_term (`λ t)%term    := (`λ S_term t)%term;
  S_term (t₁ ⋅ t₂)%term := (S_term t₁ ⋅ S_term t₂)%term;
  S_term (Λ t)%term     := (Λ S_term t)%term;
  S_term (Δ:=Δ) (Γ:=Γ) (t ⦗ τ' ⦘)%term
  := eq_rect _ _ (S_term t ⦗ S_type τ' ⦘)%term _ _.
Next Obligation.
  unfold "_ `[[ _ ]]".
  rewrite S_type_subs.
  clear S_term t. rename τ4 into τ.
  funelim (S_type τ).
  - rewrite S_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    rewrite exts_type_equation_2.
    rewrite sub_type_helper_equation_2.
    funelim (sub_type_helper τ' n).
    + rewrite sub_type_helper_equation_1.
      admit. (* problem :(. *)
    + rewrite sub_type_helper_equation_2. reflexivity.
  - 
Abort.

Definition map_has : forall (A B : Set) (f : A -> B) (l : list A) b,
    Has b (map f l) -> {a : A & f a = b & Has a l}.
Proof.
  intros A B f l.
  induction l as [| a l ih]; intros b h; cbn in *.
  - inv h.
  - destruct h as [h | h].
    + exact (existT2 _ _ a h (inl eq_refl)).
    + apply ih in h as [a' fab hasa].
      exact (existT2 _ _ a' fab (inr hasa)).
Defined.

Definition S_Renamer : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Has τ Γ₂) ->
    forall τ : type (S Δ), Has τ (map S_type Γ₁) -> Has τ (map S_type Γ₂).
Proof.
  intros Δ Γ₁ Γ₂ f τ h.
  apply map_has in h as [τ' τ'eq h]; subst.
  apply has_map,f,h.
Defined.
          
Equations Rename : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Has τ Γ₂) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  Rename ρ (Id _ _ has) := Id _ _ (ρ _ has);
  Rename ρ (λ σ ⇒ t)%term := (λ σ ⇒ Rename (ext' ρ σ) t)%term;
  Rename ρ (t₁ ⋅ t₂)%term := (Rename ρ t₁ ⋅ Rename ρ t₂)%term;
  Rename ρ (Λ t)%term     := (Λ Rename (S_Renamer ρ) t)%term;
  Rename ρ (t ⦗ τ ⦘)%term := ((Rename ρ t) ⦗ τ ⦘)%term.

Definition exts : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
    forall (ρ τ : type Δ), Has τ (ρ :: Γ₁) -> ρ :: Γ₂ ⊢ τ.
Proof.
  cbn; intros Δ Γ₁ Γ₂ σ ρ τ [h | h]; subst.
  - refine (Id _ τ _); cbn; left; reflexivity.
  - refine (Rename _ (σ _ h)).
    intros α has; cbn; right; exact has.
Defined.

Definition S_subs : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
    forall (τ : type (S Δ)), Has τ (map S_type Γ₁) -> map S_type Γ₂ ⊢ τ.
Proof.
  intros Δ Γ₁ Γ₂ σ τ h.
  apply map_has in h as [τ' ? h]; subst.
  apply σ in h; clear σ Γ₁.
  (*apply S_term, h.*)
Admitted.

Equations subs : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  subs σ (Id _ _ h)     := σ _ h;
  subs σ (λ τ ⇒ t)%term := (λ τ ⇒ subs (exts σ τ) t)%term;
  subs σ (t₁ ⋅ t₂)%term := (subs σ t₁ ⋅ subs σ t₂)%term;
  subs σ (Λ t)%term     := (Λ subs (S_subs σ) t)%term;
  subs σ (t ⦗ τ ⦘)%term := (subs σ t ⦗ τ ⦘)%term.
