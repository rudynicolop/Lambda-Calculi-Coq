From Lambda.Util Require Export Lists EqRect.
Require Coq.Vectors.Fin.

(** * System F *)

Equations mapply : forall {A : nat -> Type} (m : nat),
    (forall {n : nat}, A n -> A (S n)) -> forall {n : nat}, A n -> A (m + n) :=
  mapply  O    f a := a;
  mapply (S k) f a := f _ (mapply k f a).

Lemma f_equal_id : forall (A : Type) (x y : A) (h : x = y),
    f_equal id h = h.
Proof.
  intros A x y h.
  destruct h; reflexivity.
Defined.

Equations Derive Signature NoConfusion NoConfusionHom Subterm for Fin.t.

Inductive type (Δ : nat) : Type :=
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
Notation "x '→' y"
  := (TArrow x y) (at level 19, right associativity) : ty_scope.

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

Equations ext_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> Fin.t Δ₂) -> Fin.t (S Δ₁) -> Fin.t (S Δ₂) :=
  ext_type _  Fin.F1    := Fin.F1;
  ext_type ρ (Fin.FS n) := Fin.FS (ρ n).

Equations rename_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> Fin.t Δ₂) -> type Δ₁ -> type Δ₂ :=
  rename_type ρ (TId n) := ρ n;
  rename_type ρ (∀ τ)%ty := (∀ rename_type (ext_type ρ) τ)%ty;
  rename_type ρ (τ → τ')%ty := (rename_type ρ τ → rename_type ρ τ')%ty.

Equations exts_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> type Δ₂) -> Fin.t (S Δ₁) -> type (S Δ₂) :=
  exts_type σ Fin.F1     := Fin.F1;
  exts_type σ (Fin.FS n) := rename_type Fin.FS (σ n).

Equations subs_type : forall {Δ₁ Δ₂ : nat},
    (Fin.t Δ₁ -> type Δ₂) -> type Δ₁ -> type Δ₂ :=
  subs_type σ (TId n)     := σ n;
  subs_type σ (∀ τ)%ty    := (∀ subs_type (exts_type σ) τ)%ty;
  subs_type σ (τ → τ')%ty := (subs_type σ τ → subs_type σ τ')%ty.

Equations sub_type_helper : forall {Δ : nat}, type Δ -> Fin.t (S Δ) -> type Δ :=
  sub_type_helper τ Fin.F1     := τ;
  sub_type_helper _ (Fin.FS n) := n.

Definition sub_type {Δ : nat} (body : type (S Δ)) (arg : type Δ) : type Δ :=
  subs_type (sub_type_helper arg) body.

Notation "x '`[[' y ']]'"
  := (sub_type x y) (at level 12, left associativity) : ty_scope.

Equations mapply_ext_type : forall {Δ₁ Δ₂ : nat} (m : nat),
    (Fin.t Δ₁ -> Fin.t Δ₂) -> Fin.t (m + Δ₁) -> Fin.t (m + Δ₂) :=
  mapply_ext_type  O    ρ := ρ;
  mapply_ext_type (S k) ρ := ext_type (mapply_ext_type k ρ).

Lemma mapply_ext_type_eq
  : forall {Δ₁ Δ₂ : nat} (m : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (X : Fin.t (m + Δ₁)),
    ext_type
      (mapply_ext_type m ρ)
      (eq_rect
         _ _
         (mapply_ext_type m Fin.FS X) _
         (eq_sym (plus_n_Sm _ _)))
    = eq_rect
        _ _
        (mapply_ext_type m Fin.FS (mapply_ext_type m ρ X)) _
        (eq_sym (plus_n_Sm _ _)).
Proof.
  intros Δ₁ Δ₂ m ρ X.
  funelim (mapply_ext_type m Fin.FS); cbn in *.
  - do 3 rewrite mapply_ext_type_equation_1.
    unfold eq_sym.
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₂0) (x:=plus_n_Sm 0 Δ₂0); cbn.
    depelim X; rewrite ext_type_equation_2; reflexivity.
  - do 3 rewrite mapply_ext_type_equation_2.
    pose proof Peano_dec.UIP_nat
         _ _ (eq_sym (plus_n_Sm (S k) Δ₁)) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (eq_sym (plus_n_Sm k Δ₁))).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (eq_sym (plus_n_Sm (S k) Δ₂0)) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (eq_sym (plus_n_Sm k Δ₂0))).
    rewrite h; clear h.
    depelim X.
    + do 2 rewrite ext_type_equation_1. clear H.
      destruct (plus_n_Sm k Δ₁).
      destruct (plus_n_Sm k Δ₂0). reflexivity.
    + do 2 rewrite ext_type_equation_2.
      rewrite map_subst_map.
      do 2 rewrite ext_type_equation_2.
      rewrite map_subst_map.
      rewrite H. reflexivity.
Qed.

Print Assumptions mapply_ext_type_eq.

Lemma mapply_ext_type_eq_rect_zwei :
  forall {Δ₁ Δ₂ : nat} (m : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (X : Fin.t (m + Δ₁)),
    eq_rect_zwei
      (T:=fun u v => Fin.t u -> Fin.t v)
      (plus_n_Sm m Δ₁)
      (plus_n_Sm m Δ₂)
      (mapply_ext_type (S m) ρ)
      (mapply_ext_type m Fin.FS X)
    = mapply_ext_type m Fin.FS (mapply_ext_type m ρ X).
Proof.
  intros Δ₁ Δ₂ m ρ X.
  funelim (mapply_ext_type m Fin.FS); cbn in *.
  - rewrite mapply_ext_type_equation_2.
    do 3 rewrite mapply_ext_type_equation_1.
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₂0) (x:=plus_n_Sm 0 Δ₂0); cbn.
    rewrite eq_rect_zwei_equation_1.
    rewrite ext_type_equation_2. reflexivity.
  - repeat rewrite mapply_ext_type_equation_2.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₁) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm k Δ₁)).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₂0) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm k Δ₂0)).
    rewrite h; clear h.
    rewrite map_subst_map_zwei_both.
    depelim X; cbn.
    + do 2 rewrite ext_type_equation_1; reflexivity.
    + do 4 rewrite ext_type_equation_2.
      specialize H with (ρ:=ρ0) (X:=X).
      rewrite mapply_ext_type_equation_2 in H.
      rewrite H; reflexivity.
Defined.

Print Assumptions mapply_ext_type_eq_rect_zwei.

Lemma mapply_rename_type_ext_type :
  forall {Δ₁ Δ₂ : nat} (m : nat) (τ : type (m + Δ₁)) (ρ : Fin.t Δ₁ -> Fin.t Δ₂),
    @rename_type (m + S Δ₁) (m + S Δ₂)
                 (eq_rect_zwei
                    (T:=fun u v => Fin.t u -> Fin.t v)
                    (plus_n_Sm m Δ₁) (plus_n_Sm m Δ₂) (mapply_ext_type (S m) ρ))
      (@rename_type (m + Δ₁) (m + S Δ₁) (mapply_ext_type m Fin.FS) τ)
    = rename_type
        (mapply_ext_type m Fin.FS)
        (rename_type (mapply_ext_type m ρ) τ).
Proof.
  intros Δ₁ Δ₂ m τ.
  generalize dependent Δ₂.
  depind τ; intros Δ₂ ρ.
  - do 4 rewrite rename_type_equation_1.
    rewrite mapply_ext_type_eq_rect_zwei; reflexivity.
  - do 4 rewrite rename_type_equation_2; f_equal.
    specialize IHτ with (m:=S m) (τ:=τ) (Δ₂:=Δ₂) (ρ:=ρ).
    repeat rewrite mapply_ext_type_equation_2 in *.
    assert
      (doh : {| pr1 := S m + Δ₁; pr2 := τ |}
             = {| pr1 := S (m + Δ₁); pr2 := τ |})
      by reflexivity.
    apply IHτ in doh as IH; clear IHτ doh.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₁) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₁)).
    rewrite h in IH; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₂) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₂)).
    rewrite h in IH; clear h; cbn in *.
    rewrite <- IH; clear IH.
    rewrite map_subst_map_zwei_both. reflexivity.
  - do 4 rewrite rename_type_equation_3.
    rewrite IHτ1, IHτ2; reflexivity.
Defined.

Print Assumptions mapply_rename_type_ext_type.

Lemma rename_type_ext_type : forall {Δ₁ Δ₂ : nat} (τ : type Δ₁) (ρ : Fin.t Δ₁ -> Fin.t Δ₂),
    rename_type (ext_type ρ) (rename_type Fin.FS τ)
    = rename_type Fin.FS (rename_type ρ τ).
Proof.
  intros Δ₁ Δ₂ τ ρ.
  pose proof mapply_rename_type_ext_type 0 τ ρ as h.
  rewrite mapply_ext_type_equation_2 in h.
  do 3 rewrite mapply_ext_type_equation_1 in h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁) in h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂) in h; cbn.
  rewrite eq_rect_zwei_equation_1 in h.
  assumption.
Defined.

Lemma map_rename_typ_ext : forall {Δ₁ Δ₂ : nat} (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (Γ : list (type Δ₁)),
    map (rename_type (ext_type ρ)) (map (rename_type Fin.FS) Γ)
    = map (rename_type Fin.FS) (map (rename_type ρ) Γ).
Proof.
  intros Δ₁ Δ₂ ρ Γ.
  induction Γ as [| τ Γ ih]; cbn; f_equal; auto.
  rewrite rename_type_ext_type; reflexivity.
Defined.

Equations mapply_exts_type : forall {Δ₁ Δ₂ : nat} (m : nat),
    (Fin.t Δ₁ -> type Δ₂) -> Fin.t (m + Δ₁) -> type (m + Δ₂) :=
  mapply_exts_type  O    σ := σ;
  mapply_exts_type (S k) σ := exts_type (mapply_exts_type k σ).

Lemma mapply_subs_type_helper :
  forall (m : nat) {Δ₁ Δ₂ : nat} (ρ : Fin.t Δ₁ -> Fin.t Δ₂)
    (X : Fin.t (S m + Δ₁)) (τ' : type Δ₁),
    eq_rect_zwei
      (T:=fun u v => Fin.t u -> type v)
      (eq_sym (plus_n_Sm m Δ₂)) eq_refl
      (mapply_exts_type
         m
         (sub_type_helper (rename_type ρ τ')))
      (mapply_ext_type (S m) ρ X)
    = rename_type
        (mapply_ext_type m ρ)
        (eq_rect_zwei
           (T:=fun u v => Fin.t u -> type v)
           (eq_sym (plus_n_Sm m Δ₁)) eq_refl
           (mapply_exts_type m (sub_type_helper τ')) X).
Proof.
  intros m; induction m as [| m ih];
    intros Δ₁ Δ₂ ρ X τ'; cbn in *.
  - rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂); cbn.
    do 2 rewrite eq_rect_zwei_equation_1.
    rewrite mapply_ext_type_equation_2.
    rewrite mapply_ext_type_equation_1.
    do 2 rewrite mapply_exts_type_equation_1.
    funelim (ext_type ρ X).
    + rewrite ext_type_equation_1.
      do 2 rewrite sub_type_helper_equation_1.
      reflexivity.
    + rewrite ext_type_equation_2.
      do 2 rewrite sub_type_helper_equation_2.
      rewrite rename_type_equation_1; reflexivity.
  - pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₁) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₁)).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₂) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₂)).
    rewrite h; clear h.
    do 2 rewrite eq_sym_map_distr.
    Set Printing Implicit.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (m + Δ₁))) as h; cbn in h.
    specialize h with
      (p2:=f_equal S eq_refl).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (m + Δ₂))) as h; cbn in h.
    specialize h with
      (p2:=f_equal S eq_refl).
    rewrite h; clear h.
    Unset Printing Implicit.
    do 2 rewrite mapply_ext_type_equation_2.
    do 2 rewrite mapply_exts_type_equation_2.
    depelim X.
    + clear ih. rewrite ext_type_equation_1.
      do 2 rewrite map_subst_map_zwei_both.
      destruct m as [| m].
      * rewrite Eqdep_dec.UIP_refl_nat
          with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
        rewrite Eqdep_dec.UIP_refl_nat
          with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂); cbn.
        do 2 rewrite eq_rect_zwei_equation_1.
        do 2 rewrite exts_type_equation_1.
        rewrite rename_type_equation_1.
        rewrite ext_type_equation_1.
        reflexivity.
      * pose proof Peano_dec.UIP_nat
             _ _ (plus_n_Sm (S m) Δ₁) as h; cbn in h.
        specialize h with
          (p2:=f_equal S (plus_n_Sm m Δ₁)).
        rewrite h; clear h.
        pose proof Peano_dec.UIP_nat
             _ _ (plus_n_Sm (S m) Δ₂) as h; cbn in h.
        specialize h with
          (p2:=f_equal S (plus_n_Sm m Δ₂)).
        rewrite h; clear h; cbn.
        rewrite eq_sym_map_distr with (f:=S) (e:=plus_n_Sm m Δ₂).
        Set Printing Implicit.
        pose proof Peano_dec.UIP_nat
             _ _ (@eq_refl _ (S (m + Δ₁))) as h; cbn in h.
        specialize h with
          (p2:=f_equal S eq_refl).
        rewrite h; clear h.
        pose proof Peano_dec.UIP_nat
             _ _ (@eq_refl _ (S (m + Δ₂))) as h; cbn in h.
        specialize h with
          (p2:=f_equal S eq_refl).
        rewrite h; clear h.
        Unset Printing Implicit.
        do 2 rewrite mapply_exts_type_equation_2.
        rewrite map_subst_map_zwei_both.
        do 2 rewrite exts_type_equation_1.
        rewrite rename_type_equation_1,
          ext_type_equation_1; reflexivity.
    + rewrite ext_type_equation_2.
      do 2 rewrite map_subst_map_zwei_both.
      do 2 rewrite exts_type_equation_2.
      rewrite rename_type_ext_type,<- ih; reflexivity.
Defined.
    
Lemma mapply_subs_type_exts_type :
  forall {Δ₁ Δ₂ : nat} (m : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂)
    (τ : type (S m + Δ₁)) (τ' : type Δ₁),
    subs_type
      (Δ₁:=S m + Δ₂)
      (Δ₂:=m + Δ₂)
      (eq_rect_zwei
         (T:=fun u v => Fin.t u -> type v)
         (eq_sym (plus_n_Sm m Δ₂))
         eq_refl
         (mapply_exts_type
            m
            (sub_type_helper
               (rename_type
                  (Δ₁:=Δ₁) (Δ₂:=Δ₂) ρ τ'))))
      (rename_type
         (Δ₁:=S m + Δ₁) (Δ₂:=S m + Δ₂)
         (mapply_ext_type (S m) ρ) τ)
    = rename_type
        (Δ₁:=m + Δ₁)
        (Δ₂:=m + Δ₂)
        (mapply_ext_type m ρ)
        (subs_type
           (Δ₁:=S m + Δ₁)
           (Δ₂:=m + Δ₁)
           (eq_rect_zwei
              (T:=fun u v => Fin.t u -> type v)
              (eq_sym (plus_n_Sm m Δ₁))
              eq_refl
              (mapply_exts_type
                 m (sub_type_helper τ')))
           τ).
Proof.
  intros Δ₁ Δ₂ m ρ τ; generalize dependent Δ₂.
  depind τ; intros Δ₂ ρ τ'; cbn in *.
  - rewrite rename_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    rewrite mapply_subs_type_helper; reflexivity.
  - rewrite rename_type_equation_2.
    do 2 rewrite subs_type_equation_2.
    rewrite rename_type_equation_2; f_equal.
    specialize IHτ with (Δ₁:=Δ₁) (m:=S m) (τ:=τ).
    pose proof IHτ eq_refl as ih; clear IHτ.
    specialize ih with Δ₂ ρ τ'; cbn in *.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₁) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₁)).
    rewrite h in ih; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S m) Δ₂) as h; cbn in h.
    specialize h with
      (p2:=f_equal S (plus_n_Sm m Δ₂)).
    rewrite h in ih; clear h.
    do 2 rewrite eq_sym_map_distr in ih.
    Set Printing Implicit.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (m + Δ₁))) as h; cbn in h.
    specialize h with
      (p2:=f_equal S eq_refl).
    rewrite h in ih; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (m + Δ₂))) as h; cbn in h.
    specialize h with
      (p2:=f_equal S eq_refl).
    rewrite h in ih; clear h.
    Unset Printing Implicit.
    repeat rewrite mapply_ext_type_equation_2 in *.
    repeat rewrite mapply_exts_type_equation_2 in *.
    do 2 rewrite map_subst_map_zwei_both in ih.
    rewrite <- ih. reflexivity.
  - rewrite rename_type_equation_3.
    do 2 rewrite subs_type_equation_3.
    rewrite rename_type_equation_3; f_equal; eauto.
Defined.

Lemma rename_type_distr_sub_type :
  forall {Δ₁ Δ₂ : nat} (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (τ : type (S Δ₁)) (τ' : type Δ₁),
    (rename_type (ext_type ρ) τ `[[ rename_type ρ τ']])%ty
    = rename_type ρ (τ `[[ τ']])%ty.
Proof.
  intros Δ₁ Δ₂ ρ τ τ'; unfold "_ `[[ _ ]]".
  pose proof mapply_subs_type_exts_type 0 ρ τ τ' as h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁) in h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂) in h.
  do 2 rewrite eq_rect_zwei_equation_1 in h.
  rewrite mapply_ext_type_equation_2 in h.
  rewrite mapply_ext_type_equation_1 in h.
  do 2 rewrite mapply_exts_type_equation_1 in h.
  assumption.
Defined.

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term : forall {Δ : nat}, list (type Δ) -> type Δ -> Type :=
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
  map (rename_type Fin.FS) Γ ⊢ τ ->
  Γ ⊢ (∀ τ)%ty
| TypApp {Δ : nat} (Γ : list (type Δ)) (τ : type (S Δ)) (τ' : type Δ) :
  Γ ⊢ (∀ τ)%ty ->
  Γ ⊢ (τ `[[ τ' ]])%ty
where "Γ '⊢' τ" := (term Γ τ).

Derive Signature for term.
Equations Derive NoConfusion (* NoConfusionHom *) (*Subterm*) for term.

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

Definition ext_Renamer : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Has τ Γ₂) -> forall τ : type (S Δ),
      Has τ (map (rename_type Fin.FS) Γ₁) ->
      Has τ (map (rename_type Fin.FS) Γ₂).
Proof.
  intros Δ Γ₁ Γ₂ f τ h.
  apply map_has in h as [τ' τ'eq h]; subst.
  apply has_map,f,h.
Defined.
          
Equations Rename : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall {τ : type Δ}, Has τ Γ₁ -> Has τ Γ₂) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  Rename ρ (Id _ _ has) := Id _ _ (ρ _ has);
  Rename ρ (λ σ ⇒ t)%term := (λ σ ⇒ Rename (ext_has ρ σ) t)%term;
  Rename ρ (t₁ ⋅ t₂)%term := (Rename ρ t₁ ⋅ Rename ρ t₂)%term;
  Rename ρ (Λ t)%term     := (Λ Rename (ext_Renamer ρ) t)%term;
  Rename ρ (t ⦗ τ ⦘)%term := ((Rename ρ t) ⦗ τ ⦘)%term.

Equations exts : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall {τ : type Δ}, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
    forall {ρ τ : type Δ}, Has τ (ρ :: Γ₁) -> ρ :: Γ₂ ⊢ τ :=
  exts σ HasO := Id _ _ HasO;
  exts σ (HasS hs) := Rename (fun τ => HasS (a:=τ)) (σ _ hs).

Equations Rename_type :
  forall {Δ₁ Δ₂ : nat} {Γ : list (type Δ₁)}
    (ρ : Fin.t Δ₁ -> Fin.t Δ₂) {τ : type Δ₁},
    Γ ⊢ τ -> map (rename_type ρ) Γ ⊢ rename_type ρ τ :=
  Rename_type ρ (Id _ _ h) := Id _ _ (has_map (rename_type ρ) h);
  Rename_type ρ (`λ t)%term := (`λ Rename_type ρ t)%term;
  Rename_type ρ (t ⋅ t')%term := (Rename_type ρ t ⋅ Rename_type ρ t')%term;
  Rename_type (Δ₁:=Δ₁) (Δ₂:=Δ₂) (Γ:=Γ) ρ (TypAbs _ τ t) :=
    (Λ eq_rect
       (map (rename_type (ext_type ρ)) (map (rename_type Fin.FS) Γ))
       (fun Γ => Γ ⊢ rename_type (ext_type ρ) τ)
       (Rename_type (ext_type ρ) t)
       (map (rename_type Fin.FS) (map (rename_type ρ) Γ)) _)%term;
  Rename_type (Δ₁:=Δ₁) (Δ₂:=Δ₂) (Γ:=Γ) ρ (TypApp _ τ τ' t)%term :=
    eq_rect
      (rename_type (ext_type ρ) τ `[[ rename_type ρ τ']])%ty
      (fun τ => map (rename_type ρ) Γ ⊢ τ)
      (Rename_type ρ t ⦗ rename_type ρ τ' ⦘)%term
      (rename_type ρ (τ `[[ τ']])%ty) _.
Next Obligation. apply map_rename_typ_ext. Defined.
Next Obligation. apply rename_type_distr_sub_type. Defined.

Print Assumptions Rename_type.

Definition exts_Rename_type : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) -> forall τ : type (S Δ),
      Has τ (map (rename_type Fin.FS) Γ₁) ->
      map (rename_type Fin.FS) Γ₂ ⊢ τ.
Proof.
  intros Δ Γ₁ Γ₂ σ τ h.
  apply map_has in h as [τ₁ ? h]; subst.
  apply Rename_type,σ,h.
Defined.

Equations subs : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall {τ : type Δ}, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  subs σ (Id _ _ h)     := σ _ h;
  subs σ (λ τ ⇒ t)%term := (λ τ ⇒ subs (fun τ => exts σ (τ:=τ)) t)%term;
  subs σ (t₁ ⋅ t₂)%term := (subs σ t₁ ⋅ subs σ t₂)%term;
  subs σ (Λ t)%term     := (Λ subs (exts_Rename_type σ) t)%term;
  subs σ (t ⦗ τ ⦘)%term := (subs σ t ⦗ τ ⦘)%term.

Print Assumptions subs.

Equations sub_helper : forall {Δ : nat} {Γ : list (type Δ)} {τ : type Δ},
    Γ ⊢ τ -> forall τ' : type Δ, Has τ' (τ :: Γ) -> Γ ⊢ τ' :=
  sub_helper t _ HasO := t;
  sub_helper _ _ (HasS hs) := Id _ _ hs.

Definition sub {Δ : nat} {Γ : list (type Δ)} {τ τ' : type Δ}
           (body : τ :: Γ ⊢ τ') (arg : Γ ⊢ τ) : Γ ⊢ τ' :=
  subs (sub_helper arg) body.

Notation "x '[[' y ']]'"
  := (sub x y) (at level 38, left associativity) : term_scope.

Lemma mapply_exts_type_rename_type :
  forall (k : nat) {Δ₁ Δ₂ : nat} (X : Fin.t (k + Δ₁))
    (σ : Fin.t Δ₁ -> type Δ₂),
    eq_rect_zwei
      (T:=fun u v => Fin.t u -> type v)
      (plus_n_Sm _ _)
      (plus_n_Sm _ _)
      (mapply_exts_type (S k) σ)
      (mapply_ext_type k Fin.FS X)
    = rename_type (mapply_ext_type k Fin.FS) (mapply_exts_type k σ X).
Proof.
  intro k; induction k as [| k ih]; intros Δ₁ Δ₂ X σ; cbn in *.
  - rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂); cbn.
    rewrite mapply_exts_type_equation_2.
    rewrite mapply_exts_type_equation_1.
    do 2 rewrite mapply_ext_type_equation_1.
    rewrite eq_rect_zwei_equation_1.
    rewrite exts_type_equation_2; reflexivity.
  - pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₁) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₁)).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₂) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₂)).
    rewrite h; clear h.
    do 2 rewrite mapply_exts_type_equation_2.
    rewrite map_subst_map_zwei_both.
    do 2 rewrite mapply_ext_type_equation_2.
    depelim X.
    + clear ih.
      rewrite ext_type_equation_1.
      do 2 rewrite exts_type_equation_1.
      rewrite rename_type_equation_1.
      rewrite ext_type_equation_1.
      reflexivity.
    + rewrite ext_type_equation_2.
      do 2 rewrite exts_type_equation_2.
      specialize ih with (X:=X) (σ:=σ).
      rewrite mapply_exts_type_equation_2 in ih; cbn in *.
      rewrite ih; clear ih.
      rewrite rename_type_ext_type; reflexivity.
Defined.
 
Lemma mapply_subs_rename_type :
  forall {Δ₁ Δ₂ : nat} (k : nat) (τ : type (k + Δ₁))
    (σ : Fin.t Δ₁ -> type Δ₂),
    subs_type
      (eq_rect_zwei
         (T:=fun u v => Fin.t u -> type v)
         (plus_n_Sm _ _) (plus_n_Sm _ _)
         (mapply_exts_type (S k) σ))
      (rename_type (mapply_ext_type k Fin.FS) τ)
    = rename_type
        (mapply_ext_type k Fin.FS)
        (subs_type (mapply_exts_type k σ) τ).
Proof.
  intros Δ₁ Δ₂ k τ; generalize dependent Δ₂.
  depind τ; intros Δ₂ σ.
  - rewrite rename_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    rewrite mapply_exts_type_rename_type; reflexivity.
  - rewrite rename_type_equation_2.
    do 2 rewrite subs_type_equation_2.
    rewrite rename_type_equation_2; f_equal.
    specialize IHτ with (Δ₁:=Δ₁) (k:=S k) (τ:=τ).
    pose proof IHτ eq_refl as ih; clear IHτ.
    specialize ih with (Δ₂:=Δ₂) (σ:=σ).
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₁) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₁)).
    rewrite h in ih; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₂) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₂)).
    rewrite h in ih; clear h.
    do 2 rewrite mapply_ext_type_equation_2 in ih.
    do 2 rewrite mapply_exts_type_equation_2 in ih. cbn in *.
    rewrite <- ih; clear ih.
    rewrite map_subst_map_zwei_both,
      mapply_exts_type_equation_2; reflexivity.
  - rewrite rename_type_equation_3.
    do 2 rewrite subs_type_equation_3.
    rewrite rename_type_equation_3; f_equal; auto.
Defined.
    
Lemma subs_rename_type :
  forall {Δ₁ Δ₂ : nat} (σ : Fin.t Δ₁ -> type Δ₂) (τ : type Δ₁),
    subs_type (exts_type σ) (rename_type Fin.FS τ)
    = rename_type Fin.FS (subs_type σ τ).
Proof.
  intros Δ₁ Δ₂ σ τ.
  pose proof mapply_subs_rename_type 0 τ σ as h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁) in h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂) in h; cbn in h.
  rewrite mapply_exts_type_equation_2,
    mapply_exts_type_equation_1 in h.
  do 2 rewrite mapply_ext_type_equation_1 in h.
  rewrite eq_rect_zwei_equation_1 in h.
  assumption.
Defined.
  
Lemma map_subs_rename_type :
  forall {Δ₁ Δ₂ : nat} (Γ : list (type Δ₁))
    (σ : Fin.t Δ₁ -> type Δ₂),
    map (subs_type (exts_type σ)) (map (rename_type Fin.FS) Γ)
    = map (rename_type Fin.FS) (map (subs_type σ) Γ).
Proof.
  intros Δ₁ Δ₂ Γ σ.
  induction Γ as [| τ Γ ih]; cbn in *; f_equal; auto using subs_rename_type.
Defined.

Print Assumptions map_subs_rename_type.

Lemma mapply_exts_type_idem :
  forall (k : nat) {Δ : nat} (X : Fin.t (k + Δ)) (τ' : type Δ),
    mapply_exts_type
      k (sub_type_helper τ')
      (mapply_ext_type k Fin.FS X) = X.
Proof.
  intro k;
    induction k as [| k ih];
    intros Δ X τ'.
  - rewrite mapply_exts_type_equation_1,
      mapply_ext_type_equation_1,
      sub_type_helper_equation_2; reflexivity.
  - rewrite mapply_exts_type_equation_2,
      mapply_ext_type_equation_2.
    depelim X.
    + rewrite ext_type_equation_1,
        exts_type_equation_1; reflexivity.
    + rewrite ext_type_equation_2,
        exts_type_equation_2.
      rewrite ih, rename_type_equation_1; reflexivity.
Defined.

Lemma mapply_exts_type_subs_type_rename_type_idem :
  forall {Δ : nat} (k : nat) (τ : type (k + Δ)) (τ' : type Δ),
    subs_type
      (mapply_exts_type k (sub_type_helper τ'))
      (rename_type (mapply_ext_type k Fin.FS) τ) = τ.
Proof.
  intros Δ k τ τ'; depind τ.
  - rewrite rename_type_equation_1,
      subs_type_equation_1,
      mapply_exts_type_idem;
      reflexivity.
  - specialize IHτ with (Δ:=Δ0) (k:=S k) (τ:=τ) (τ':=τ').
    pose proof IHτ eq_refl as ih; clear IHτ.
    rewrite rename_type_equation_2,
      subs_type_equation_2; f_equal.
    rewrite mapply_exts_type_equation_2,
      mapply_ext_type_equation_2 in ih.
    cbn in *; assumption.
  - rewrite rename_type_equation_3,
      subs_type_equation_3; f_equal; auto.
Defined.

Lemma subs_type_rename_type_idem :
  forall {Δ : nat} (τ τ' : type Δ),
    subs_type (sub_type_helper τ') (rename_type Fin.FS τ) = τ.
Proof.
  intros Δ τ τ'.
  pose proof
       mapply_exts_type_subs_type_rename_type_idem
       0 τ τ' as h.
  rewrite mapply_exts_type_equation_1,
    mapply_ext_type_equation_1 in h;
    assumption.
Defined.

Lemma map_subs_type_rename_type_idem :
  forall {Δ : nat} (τ' : type Δ) (Γ : list (type Δ)),
    map
      (subs_type (sub_type_helper τ'))
      (map (rename_type Fin.FS) Γ) = Γ.
Proof.
  intros Δ τ' Γ; induction Γ as [| τ Γ ih]; cbn;
    f_equal; auto using subs_type_rename_type_idem.
Defined.

Lemma subs_type_mapply_exts_type_eq_rect_zwei :
  forall (k : nat) {Δ₁ Δ₂ : nat} (X : Fin.t (S k + Δ₁))
    (τ' : type Δ₁) (σ : Fin.t Δ₁ -> type Δ₂),
    subs_type
      (eq_rect_zwei
         (T:=fun u v => Fin.t u -> type v)
         (eq_sym (plus_n_Sm k Δ₂)) eq_refl
         (mapply_exts_type k (sub_type_helper (subs_type σ τ'))))
      (mapply_exts_type (S k) σ X)
    = subs_type
        (mapply_exts_type k σ)
        (eq_rect_zwei
           (T:=fun u v => Fin.t u -> type v)
           (eq_sym (plus_n_Sm k Δ₁)) eq_refl
           (mapply_exts_type k (sub_type_helper τ')) X).
Proof.
  intro k; induction k as [| k ih];
    intros Δ₁ Δ₂ X τ' σ.
  - rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁).
    rewrite Eqdep_dec.UIP_refl_nat
      with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂); cbn.
    rewrite mapply_exts_type_equation_2.
    do 3 rewrite mapply_exts_type_equation_1.
    do 2 rewrite eq_rect_zwei_equation_1.
    depelim X.
    + rewrite exts_type_equation_1,
        subs_type_equation_1.
      do 2 rewrite sub_type_helper_equation_1; reflexivity.
    + rewrite exts_type_equation_2,
        sub_type_helper_equation_2,
        subs_type_equation_1,
        subs_type_rename_type_idem; reflexivity.
  - pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₁) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₁)).
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₂) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₂)).
    rewrite h; clear h; cbn in *.
    do 2 rewrite eq_sym_map_distr.
    Set Printing Implicit.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (k + Δ₂))) (f_equal S eq_refl) as h.
    rewrite h; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (k + Δ₁))) (f_equal S eq_refl) as h.
    rewrite h; clear h.
    Unset Printing Implicit.
    do 4 rewrite mapply_exts_type_equation_2.
    do 2 rewrite map_subst_map_zwei_both.
    depelim X.
    + do 2 rewrite exts_type_equation_1.
      do 2 rewrite subs_type_equation_1.
      do 2 rewrite exts_type_equation_1; reflexivity.
    + do 2 rewrite exts_type_equation_2.
      specialize ih with Δ₁ Δ₂ X τ' σ.
      do 2 rewrite subs_rename_type; f_equal.
      rewrite <- ih; clear ih.
      rewrite mapply_exts_type_equation_2; reflexivity.
Defined.
    
Lemma mapply_exts_type_subs_mapply_ext_type :
      forall {Δ₁ Δ₂ : nat} (k : nat) (τ : type (S k + Δ₁))
        (τ' : type Δ₁) (σ : Fin.t Δ₁ -> type Δ₂),
        subs_type
          (eq_rect_zwei
             (T:=fun u v => Fin.t u -> type v)
             (eq_sym (plus_n_Sm _ _)) eq_refl
             (mapply_exts_type k (sub_type_helper (subs_type σ τ'))))
          (subs_type (mapply_exts_type (S k) σ) τ)
        = subs_type
            (mapply_exts_type k σ)
            (subs_type
               (eq_rect_zwei
                  (T:=fun u v => Fin.t u -> type v)
                  (eq_sym (plus_n_Sm _ _)) eq_refl
                  (mapply_exts_type k (sub_type_helper τ')))
               τ).
Proof.
  intros Δ₁ Δ₂ k τ τ' σ; depind τ.
  - do 2 rewrite subs_type_equation_1.
    rewrite subs_type_mapply_exts_type_eq_rect_zwei;
      reflexivity.
  - do 4 rewrite subs_type_equation_2; f_equal.
    specialize IHτ with
      (Δ₁:=Δ₁) (Δ₂:=Δ₂) (k:=S k)
      (τ:=τ) (τ':=τ') (σ:=σ).
    pose proof IHτ eq_refl as ih; clear IHτ.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₁) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₁)).
    rewrite h in ih; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (plus_n_Sm (S k) Δ₂) as h; cbn in h.
    specialize h with (f_equal S (plus_n_Sm k Δ₂)).
    rewrite h in ih; clear h; cbn in *.
    do 2 rewrite eq_sym_map_distr in ih.
    Set Printing Implicit.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (k + Δ₂))) (f_equal S eq_refl) as h.
    rewrite h in ih; clear h.
    pose proof Peano_dec.UIP_nat
         _ _ (@eq_refl _ (S (k + Δ₁))) (f_equal S eq_refl) as h.
    rewrite h in ih; clear h.
    Unset Printing Implicit.
    do 4 rewrite mapply_exts_type_equation_2 in ih.
    do 2 rewrite map_subst_map_zwei_both in ih.
    rewrite <- ih; clear ih.
    rewrite mapply_exts_type_equation_2;reflexivity.
  - do 4 rewrite subs_type_equation_3; f_equal; eauto.
Defined.

Lemma subs_ext_type :
  forall {Δ₁ Δ₂ : nat} (σ : Fin.t Δ₁ -> type Δ₂)
    (τ : type (S Δ₁)) (τ' : type Δ₁),
    (subs_type (exts_type σ) τ `[[subs_type σ τ']])%ty
    = subs_type σ (τ `[[ τ']])%ty.
Proof.
  unfold "_ `[[ _ ]]".
  intros Δ₁ Δ₂ σ τ τ'.
  pose proof
       mapply_exts_type_subs_mapply_ext_type
       0 τ τ' σ as h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₁) (x:=plus_n_Sm 0 Δ₁) in h.
  rewrite Eqdep_dec.UIP_refl_nat
    with (n:=S Δ₂) (x:=plus_n_Sm 0 Δ₂) in h; cbn in h.
  rewrite mapply_exts_type_equation_2 in h.
  do 3 rewrite mapply_exts_type_equation_1 in h.
  do 2 rewrite eq_rect_zwei_equation_1 in h.
  assumption.
Defined.

Equations subs_type_term
  : forall {Δ₁ Δ₂ : nat} {Γ : list (type Δ₁)} {τ : type Δ₁}
      (σ : Fin.t Δ₁ -> type Δ₂),
    Γ ⊢ τ -> map (subs_type σ) Γ ⊢ subs_type σ τ :=
  subs_type_term σ (Id _ _ h) := Id _ _ (has_map (subs_type σ) h);
  subs_type_term σ (`λ t)%term := (`λ subs_type_term σ t)%term;
  subs_type_term σ (t₁ ⋅ t₂)%term
  := (subs_type_term σ t₁ ⋅ subs_type_term σ t₂)%term;
  subs_type_term (Δ₁:=Δ₁) (Δ₂:=Δ₂) σ (TypAbs Γ τ t)%term
  := let t' := subs_type_term (exts_type σ) t in
     (Λ
        eq_rect
        _ (fun Γ => Γ ⊢ subs_type (exts_type σ) τ) t' _ _)%term;
  subs_type_term (Δ₁:=Δ₁) (Δ₂:=Δ₂) σ (TypApp Γ τ τ' t)%term
  := let t' := subs_type_term σ t in
    eq_rect
      _ (fun τ => map (subs_type σ) Γ ⊢ τ)
      (t' ⦗subs_type σ τ'⦘)%term _ _.
Next Obligation. apply map_subs_rename_type. Defined.
Next Obligation.
  enough
    ((subs_type (exts_type σ) τ `[[subs_type σ τ']])%ty
     = subs_type σ (τ `[[ τ']])%ty); auto.
  apply subs_ext_type.
Defined.

Print Assumptions subs_type_term.
    
Definition sub_type_term
           {Δ : nat} {Γ : list (type Δ)} {τ : type (S Δ)}
           (body : map (rename_type Fin.FS) Γ ⊢ τ) (τ' : type Δ)
  : Γ ⊢ (τ `[[τ']])%ty :=
  eq_rect
    _ (fun Γ => Γ ⊢ τ `[[ τ' ]]%ty)
    (subs_type_term (sub_type_helper τ') body) _
    (map_subs_type_rename_type_idem τ' Γ).

Print Assumptions sub_type_term.

Notation "x '[[`' y ']]'"
  := (sub_type_term x y) (at level 38, left associativity) : term_scope.

Reserved Notation "x '-->' y" (at level 80, no associativity).

Inductive bred {Δ : nat} {Γ : list (type Δ)}
  : forall {τ : type Δ}, Γ ⊢ τ -> Γ ⊢ τ -> Prop :=
| bred_bred (τ τ' : type Δ) (t : τ :: Γ ⊢ τ') (t' : Γ ⊢ τ) :
  ((`λ t) ⋅ t')%term -->  (t [[ t' ]])%term
| bred_abs (τ τ' : type Δ) (t t' : τ :: Γ ⊢ τ') :
  t -->  t' ->
  (`λ t)%term --> (`λ t')%term
| bred_app_1 (τ τ' : type Δ) (t₁ t₁' : Γ ⊢ (τ → τ')%ty) (t₂ : Γ ⊢ τ) :
  t₁ --> t₁' ->
  (t₁ ⋅ t₂)%term --> (t₁' ⋅ t₂)%term
| bred_app_2 (τ τ' : type Δ) (t₁ : Γ ⊢ (τ → τ')%ty) (t₂ t₂' : Γ ⊢ τ) :
  t₂ --> t₂' ->
  (t₁ ⋅ t₂)%term --> (t₁ ⋅ t₂')%term
| bred_typ_abs (τ : type (S Δ)) (t t' : map (rename_type Fin.FS) Γ ⊢ τ) :
  t -->  t' ->
  (Λ t)%term --> (Λ t')%term
| bred_typ_app_inner (τ : type (S Δ)) (τ' : type Δ) (t t' : Γ ⊢ (∀ τ)%ty) :
  t -->  t' ->
  (t ⦗τ'⦘)%term -->  (t' ⦗τ'⦘)%term
| bred_typ_app (τ : type (S Δ)) (τ' : type Δ)
               (t : map (rename_type Fin.FS) Γ ⊢ τ) :
  ((Λ t) ⦗τ'⦘)%term -->  (t [[` τ']])%term
where "x '-->' y" := (bred x y).

Print Assumptions bred.

Derive Signature for bred.

Variant value {Δ : nat} {Γ : list (type Δ)}
  : forall {τ : type Δ}, Γ ⊢ τ -> Prop :=
  | Abs_value (τ τ' : type Δ) (t : τ :: Γ ⊢ τ') :
    value (`λ t)%term
  | TypAbs_value (τ : type (S Δ))
                 (t : map (rename_type Fin.FS) Γ ⊢ τ) :
    value (Λ t)%term.

Derive Signature for value.

Lemma canonical_abs :
  forall {Δ : nat} {τ τ' : type Δ} (t : [] ⊢ (τ → τ')%ty),
    value t ->
    exists body : [τ] ⊢ τ', t = (`λ body)%term.
Proof.
  intros Δ τ τ' t v; depelim v; eauto.
Qed.

Print Assumptions canonical_abs.

Lemma canonical_typabs :
  forall {Δ : nat} {Γ : list (type Δ)}
    {τ : type (S Δ)} (t : Γ ⊢ (∀ τ)%ty),
    value t ->
    exists body, t = (Λ body)%term.
Proof.
  intros Δ Γ τ t v; depelim v; eauto.
Qed.

Local Hint Constructors bred : core.
Local Hint Constructors value : core.

Theorem Progress :
  forall {Δ : nat} {τ : type Δ} (t : [] ⊢ τ),
    value t \/ exists t', t -->  t'.
Proof.
  intros Δ τ t; depind t; auto.
  - inv h.
  - right.
    destruct IHt1 as [v1 | (t1' & ih1)]; eauto.
    pose proof canonical_abs t1 v1
      as [t1' t1'eq]; subst; eauto.
  - right.
    destruct IHt as [v | (t' & ih)]; eauto.
    pose proof canonical_typabs t v
      as [t' t'eq]; subst; eauto.
Qed.

Print Assumptions Progress.
