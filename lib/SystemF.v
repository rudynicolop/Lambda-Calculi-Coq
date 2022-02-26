Require Export Lambda.Util.
From Equations Require Export Equations.

(** * System F *)

Equations len {A : Set} : list A -> nat :=
| []    => 0
| _ :: l => S (len l).

Reserved Notation "x '≤' y" (at level 80, no associativity).

Inductive LE (n : nat) : nat -> Set :=
| LE_n : n ≤ n
| LE_S m :
  n ≤ m ->
  n ≤ S m
where "x ≤ y" := (LE x y) : type_scope.

Derive Signature for LE.
Equations Derive NoConfusion (*NoConfusionHom*) (*Subterm*) for LE.

Equations S_LE : forall {n m}, n ≤ m -> S n ≤ S m :=
  S_LE (LE_n n) := LE_n (S n);
  S_LE (LE_S _ _ hnm) := LE_S _ _ (S_LE hnm).

Equations LE_0_l : forall n : nat, 0 ≤ n :=
  LE_0_l 0     := LE_n _;
  LE_0_l (S n) := LE_S _ _ (LE_0_l n).

Definition bruh (n m : nat) (ρ : forall r, r ≤ m -> r ≤ n) : m ≤ n := ρ m (LE_n m).

Equations S_impl_LE : forall {n m}, S n ≤ S m -> n ≤ m :=
  S_impl_LE (LE_n (S n)) := LE_n n;
  S_impl_LE (LE_S n (S m) h) := LE_S _ _ (S_impl_LE h).

Lemma not_S_n_LE_n : forall (n : nat), S n ≤ n -> Empty_set.
Proof.
  intros n h; induction n as [| n ih].
  - inv h.
  - apply S_impl_LE,ih in h.
    apply h.
Defined.

Lemma LE_n_eq : forall {n : nat} (h : n ≤ n), h = LE_n n.
Proof.
  intros n h; depelim h.
  - inv H. apply inj_right_pair in H1; subst. reflexivity.
  - exfalso. apply not_S_n_LE_n in h. inv h.
Defined.

Equations Derive NoConfusionHom for LE.
Next Obligation.
  unfold NoConfusionHom_LE in H.
  depelim a; depelim b; cbn in *; subst; try contradiction.
  - rewrite LE_n_eq; reflexivity.
  - reflexivity.
Defined.
Next Obligation.
  unfold noConfusionHom_LE_obligation_2,
    noConfusionHom_LE_obligation_1.
  unfold NoConfusionHom_LE in *.
  depelim a; depelim b; cbn in *; subst; try contradiction.
  - pose proof LE_n_eq b0 as b0eq; subst.
    unfold eq_ind_r,eq_ind, eq_sym,LE_n_eq.
    unfold eq_ind_r,eq_ind,eq_sym,inj_right_pair,f_equal.
    rewrite eq_dec_refl.
    unfold K_dec.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
    + depelim e; reflexivity.
    + intros x y. left.
      rewrite Eqdep_dec.UIP_refl_nat with (x := x).
      rewrite Eqdep_dec.UIP_refl_nat with (x := y).
      reflexivity.
  - unfold eq_ind_r,eq_ind, eq_sym; reflexivity.
Defined.
Next Obligation.
  unfold noConfusionHom_LE_obligation_1.
  unfold NoConfusionHom_LE in *.
  depelim b.
  - unfold eq_ind_r,eq_ind, eq_sym, LE_n_eq.
    unfold eq_ind_r,eq_ind,eq_sym,inj_right_pair,f_equal.
    rewrite eq_dec_refl.
    unfold K_dec.
    rewrite <- Eqdep_dec.eq_rect_eq_dec; try reflexivity.
    + intros x y. left.
      rewrite Eqdep_dec.UIP_refl_nat with (x := x).
      rewrite Eqdep_dec.UIP_refl_nat with (x := y).
      reflexivity.
  - unfold eq_ind_r,eq_ind, eq_sym; reflexivity.
Defined.

Equations Derive Subterm for LE.
   

Lemma LE_eq : forall {n m : nat} (h h' : n ≤ m), h = h'.
Proof.
  intros n m; generalize dependent n.
  induction m as [| m ih]; intros n h h'.
  - depelim h; depelim h'; reflexivity.
  - destruct n as [| n].
    + depelim h; depelim h'.
      pose proof ih 0 h h' as H; rewrite H; reflexivity.
    + pose proof S_impl_LE h as H.
      pose proof S_impl_LE h' as H'.
      pose
    
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

Definition LT_0_l (n : nat) : 0 `< S n := S_LE (LE_0_l n).

Definition S_impl_LT {n m : nat} : S n `< S m -> n `< m := S_impl_LE.

Equations bruh' : forall (m n : nat), (forall r, r `< m -> r `< n) -> m ≤ n :=
  bruh' 0     n _ := LE_0_l n;
  bruh' (S m) n ρ := ρ m (LE_n (S m)).

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

Equations type_eq_dec : forall {Δ : nat} (τ ρ : type Δ), {τ = ρ} + {τ <> ρ} :=
  type_eq_dec (TId n _) (TId m _) with Nat.eq_dec n m => {
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
Next Obligation.


Equations rename_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> n `< Δ₂) -> type Δ₁ -> type Δ₂ :=
  rename_type ρ (TId _ h)    := TId _ (ρ _ h);
  rename_type ρ (∀ τ)%ty     := (∀ rename_type (ext_LT ρ) τ)%ty;
  rename_type ρ (τ₁ → τ₂)%ty := (rename_type ρ τ₁ → rename_type ρ τ₂)%ty.

Definition exts_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> type Δ₂) -> forall n, n `< S Δ₁ -> type (S Δ₂).
Proof.
  intros Δ₁ Δ₂ σ n h.
  inversion h; subst.
  - refine (TId 0 (LT_0_l _)).
  - refine (rename_type (fun _ => id) (S_type (σ _ H0))).
Defined.

Equations subs_type : forall {Δ₁ Δ₂ : nat},
    (forall n, n `< Δ₁ -> type Δ₂) -> type Δ₁ -> type Δ₂ :=
  subs_type σ (TId _ hn)  := σ _ hn;
  subs_type σ (τ → τ')%ty := (subs_type σ τ → subs_type σ τ')%ty;
  subs_type σ (∀ τ)%ty    := (∀ subs_type (exts_type σ) τ)%ty.

Definition sub_type : forall {Δ : nat}, type (S Δ) -> type Δ -> type Δ.
Proof.
  intros Δ body arg.
  refine (subs_type _ body).
  clear body. intros n h.
  inversion h; subst.
  - apply arg.
  - clear arg.
    apply (TId n H0).
Defined.

Notation "x '`[[' y ']]'"
  := (sub_type x y) (at level 12, no associativity) : ty_scope.

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

Definition lookup : forall {Δ : nat} {Γ : list (type Δ)} {n : nat},
    n `< len Γ -> type Δ.
Proof.
  intros Δ Γ.
  induction Γ as [| τ Γ ih]; cbn; intros [| n] hn.
  - inv hn.
  - inv hn.
  - unfold "`<" in *.
    depelim hn.
    + apply τ.
    + rewrite len_equation_2 in H.
      injection H as h'. rewrite <- h' in hn.
      eapply ih,hn.
  - unfold "`<" in *.
    eapply ih,S_impl_LE,hn.
Defined.

Local Transparent len.

Equations lookup' :
  forall {Δ : nat} {Γ : list (type Δ)} {n : nat}, n `< len Γ -> type Δ :=
  lookup' (Γ:=τ :: _) (LE_n 1) := τ;
  lookup' (Γ:=_ :: Γ') (LE_S (S _) _ h) := lookup' (Γ:=Γ') h.

Local Opaque len.

Definition count :
  forall {Δ : nat} {Γ : list (type Δ)} {n : nat}
    (h : n `< len Γ), Has (lookup' h) Γ.
Proof.
  intros Δ Γ n h.
  funelim (lookup' h).
  - left. rewrite lookup'_equation_2. reflexivity.
  - right. (*Search (lookup' (LE_S (S _) (len _) _)).*)
    rewrite lookup'_equation_3. apply H.
Defined.

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

Definition has_map : forall (A B : Set) (f : A -> B) (l : list A) b,
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
  intros Δ Γ₁.
  induction Γ₁ as [| τ₁ Γ₁ ih]; intros [| τ₂ Γ₂] f τ h; cbn in *.
  - inv h.
  - inv h.
  - destruct h as [h | h]; subst.
    + specialize f with (τ := τ₁).
      apply f. left; reflexivity.
    + apply has_map in h as [τ' τ'eq hasτ'].
      specialize f with (τ := τ').
      apply f. right; apply hasτ'.
  - destruct h as [h | h]; subst.
    + pose proof f τ₁ (inl eq_refl) as h.
      destruct h as [h | h]; subst.
      * left; reflexivity.
      * right. apply ih.
        intros τ hτ.
        pose proof f _ (inr hτ) as h'.
        destruct h' as [h' | h']; subst.
        -- 
      
Equations Rename : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Has τ Γ₂) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  Rename ρ (Id _ _ has) := Id _ _ (ρ _ has);
  Rename ρ (λ σ ⇒ t)%term := (λ σ ⇒ Rename (ext' ρ σ) t)%term;
  Rename ρ (t₁ ⋅ t₂)%term := (Rename ρ t₁ ⋅ Rename ρ t₂)%term;
  Rename ρ (Λ t)%term     := (Λ Rename _ t)%term;
  Rename ρ (t ⦗ τ ⦘)%term := ((Rename ρ t) ⦗ τ ⦘)%term.
