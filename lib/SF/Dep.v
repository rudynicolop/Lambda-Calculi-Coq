Require Export Lambda.Util.
From Equations Require Export Equations.
Require Coq.Vectors.Fin.

(** * System F *)

Equations mapply : forall {A : nat -> Set} (m : nat),
    (forall {n : nat}, A n -> A (S n)) -> forall {n : nat}, A n -> A (m + n) :=
  mapply  O    f a := a;
  mapply (S k) f a := f _ (mapply k f a).

Lemma f_equal_id : forall (A : Set) (x y : A) (h : x = y),
    f_equal id h = h.
Proof.
  intros A x y h.
  destruct h; reflexivity.
Defined.

Module FIN.
  Export Coq.Vectors.Fin.

  Derive Signature for t.
  Equations Derive NoConfusion NoConfusionHom Subterm for t.

  Equations nat_of {n : nat} : t n -> nat :=
  | F1 := 0
  | FS f := S (nat_of f).

  Lemma nat_of_inj : forall (k : nat) (m n : t k),
      nat_of m = nat_of n -> m = n.
    intros k m; funelim (nat_of m);
      intros n h; funelim (nat_of n);
      cbn in *; try reflexivity.
    - rewrite nat_of_equation_1,nat_of_equation_2 in h.
      discriminate.
    - rewrite nat_of_equation_1,nat_of_equation_2 in h.
      discriminate.
    - do 2 rewrite nat_of_equation_2 in h.
      injection h as h'.
      apply H0 in h'; subst; reflexivity.
  Defined.

  Definition LT {k : nat} (m n : t k) : Prop :=
    nat_of m < nat_of n.

  Definition LT_eq_LT_dec {k : nat} (m n : t k)
    : {LT m n} + {m = n} + {LT n m} :=
    match lt_eq_lt_dec (nat_of m) (nat_of n) with
    | inleft (left h) => inleft (left h)
    | inleft (right h) => inleft (right (nat_of_inj _ _ _ h))
    | inright h => inright h
    end.

  (** [pred] of [m] . *)
  Equations PRED : forall {k : nat} {m n : t (S k)}, LT n m -> t k :=
    PRED (m := FS f) _ := f;
    PRED (k:=k) (m := F1) h := _.
  Next Obligation.
    unfold LT in h.
    rewrite nat_of_equation_1 in h.
    apply Nat.nlt_0_r in h. contradiction.
  Defined.
End FIN.

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
  := (sub_type x y) (at level 12, no associativity) : ty_scope.

Equations mapply_ext_type : forall {Δ₁ Δ₂ : nat} (m : nat),
    (Fin.t Δ₁ -> Fin.t Δ₂) -> Fin.t (m + Δ₁) -> Fin.t (m + Δ₂) :=
  mapply_ext_type  O    ρ := ρ;
  mapply_ext_type (S k) ρ := ext_type (mapply_ext_type k ρ).

Fail Lemma mapply_ext_type_eq
  : forall {Δ₁ Δ₂ : nat} (m : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (X : Fin.t (m + Δ₁)),
    ext_type (mapply_ext_type m ρ) (mapply_ext_type m Fin.FS X)
    = mapply_ext_type m Fin.FS (mapply_ext_type m ρ X).

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

Equations eq_rect_zwei : forall {A B : Set} {x y : A} {u v : B} {T : A -> B -> Set},
    x = y -> u = v -> T x u -> T y v :=
  eq_rect_zwei eq_refl eq_refl t := t.

Search (eq_rect _ _ _ _ (f_equal _ _)).

Lemma map_subst_map_zwei_1 :
  forall {A B C : Set} {P : A -> B -> Set} {Q : C -> B -> Set}
    (f : A -> C) (g : forall a b, P a b -> Q (f a) b)
    {x y : A} (h1 : x = y) {u v : B} (h2 : u = v) (z : P x u),
    eq_rect_zwei (f_equal f h1) h2 (g x u z) = g y v (eq_rect_zwei h1 h2 z).
Proof.
  intros A B C P Q f g x y h1 u v h2 z.
  destruct h1; destruct h2.
  do 2 rewrite eq_rect_zwei_equation_1; reflexivity.
Defined.

Lemma map_subst_map_zwei_2 :
  forall {A B C : Set} {P : A -> B -> Set} {Q : A -> C -> Set}
    (f : B -> C) (g : forall a b, P a b -> Q a (f b))
    {x y : A} (h1 : x = y) {u v : B} (h2 : u = v) (z : P x u),
    eq_rect_zwei h1 (f_equal f h2) (g x u z) = g y v (eq_rect_zwei h1 h2 z).
Proof.
  intros A B C P Q f g x y h1 u v h2 z.
  destruct h1; destruct h2.
  do 2 rewrite eq_rect_zwei_equation_1; reflexivity.
Defined.

Lemma map_subst_map_zwei_both :
  forall {A B C D : Set} {P : A -> B -> Set} {Q : C -> D -> Set}
    (f : A -> C) (h : B -> D) (g : forall a b, P a b -> Q (f a) (h b))
    {x y : A} (h1 : x = y) {u v : B} (h2 : u = v) (z : P x u),
    eq_rect_zwei (f_equal f h1) (f_equal h h2) (g x u z) = g y v (eq_rect_zwei h1 h2 z).
Proof.
  intros A B C D P Q f h g x y h1 u v h2 z.
  destruct h1; destruct h2.
  do 2 rewrite eq_rect_zwei_equation_1; reflexivity.
Defined.

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

Check @mapply_ext_type.
Check exts_type.

Equations mapply_exts_type : forall {Δ₁ Δ₂ : nat} (m : nat),
    (Fin.t Δ₁ -> type Δ₂) -> Fin.t (m + Δ₁) -> type (m + Δ₂) :=
  mapply_exts_type  O    σ := σ;
  mapply_exts_type (S k) σ := exts_type (mapply_exts_type k σ).

Fail Lemma mapply_exts_type_sub_type_helper :
  forall {Δ₁ Δ₂ : nat} (m : nat)
    (ρ : Fin.t Δ₁ -> Fin.t Δ₂)
    (X : Fin.t (S (m + Δ₁))) (τ : type Δ₁),
    mapply_exts_type
      m (sub_type_helper (rename_type ρ τ))
      (ext_type (mapply_ext_type m ρ) X)
    = rename_type
        (mapply_ext_type m ρ)
        (mapply_exts_type m (sub_type_helper τ) X).

Fail Lemma mapply_subs_type_exts_type :
  forall {Δ₁ Δ₂ : nat} (m : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂)
    (τ : type (S m + Δ₁)) (τ' : type Δ₁),
    subs_type
      (mapply_exts_type
         m (sub_type_helper (rename_type ρ τ')))
      (rename_type
         (mapply_ext_type (S m) ρ) τ)
    = rename_type
        (mapply_ext_type m ρ)
        (subs_type
           (mapply_exts_type m (sub_type_helper τ')) τ).

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
    + rewrite ext_type_equation_1.
      do 2 rewrite map_subst_map_zwei_both.
      clear ih.
      (*generalize dependent Δ₂.
      generalize dependent Δ₁.
      induction m as [| m ih]; intros Δ₁ τ' Δ₂ ρ.*)
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
    (forall τ : type Δ, Has τ Γ₁ -> Has τ Γ₂) ->
    forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  Rename ρ (Id _ _ has) := Id _ _ (ρ _ has);
  Rename ρ (λ σ ⇒ t)%term := (λ σ ⇒ Rename (ext' ρ σ) t)%term;
  Rename ρ (t₁ ⋅ t₂)%term := (Rename ρ t₁ ⋅ Rename ρ t₂)%term;
  Rename ρ (Λ t)%term     := (Λ Rename (ext_Renamer ρ) t)%term;
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

Lemma annoyed :
  forall (Δ₁ Δ₂ : nat) (ρ : Fin.t Δ₁ -> Fin.t Δ₂) (τ : type (S Δ₁)) (τ' : type Δ₁),
    (rename_type (ext_type ρ) τ `[[ rename_type ρ τ']])%ty
    = rename_type ρ (τ `[[ τ']])%ty.
Proof.
  intros Δ₁ Δ₂ ρ τ τ'.
  unfold "_ `[[ _ ]]".
  (*Check (exts_type,rename_type).
  Check rename_type.
  Print exts_type.
  Check @subs_type.*)
  Set Printing Implicit.
  (*Check rename_type.
  Check subs_type.
  Check @rename_type Δ₁ Δ₂ ρ (@subs_type (S Δ₁) Δ₁ (@sub_type_helper Δ₁ τ') τ).*)
  (*subs_type σ (rename_type ρ τ) = rename_type ρ (subs_type σ τ)*)
  funelim (rename_type (ext_type ρ) τ).
  - rewrite rename_type_equation_1.
    do 2 rewrite subs_type_equation_1.
    funelim (ext_type ρ0 n).
    + rewrite ext_type_equation_1.
      do 2 rewrite sub_type_helper_equation_1. reflexivity.
    + rewrite ext_type_equation_2.
      do 2 rewrite sub_type_helper_equation_2.
      rewrite rename_type_equation_1. reflexivity.
  - rewrite rename_type_equation_2.
    do 2 rewrite subs_type_equation_2.
    rewrite rename_type_equation_2.
    f_equal.
Admitted.

Equations Rename_type :
  forall {Δ₁ Δ₂ : nat} {Γ : list (type Δ₁)}
    (ρ : Fin.t Δ₁ -> Fin.t Δ₂) {τ : type Δ₁},
    Γ ⊢ τ -> map (rename_type ρ) Γ ⊢ rename_type ρ τ :=
  Rename_type ρ (Id _ _ h) := Id _ _ (has_map (rename_type ρ) h);
  Rename_type ρ (`λ t)%term := (`λ Rename_type ρ t)%term;
  Rename_type ρ (t ⋅ t')%term := (Rename_type ρ t ⋅ Rename_type ρ t')%term;
  Rename_type (Δ₁:=Δ₁) (Δ₂:=Δ₂) (Γ:=Γ) ρ (TypAbs _ τ t) :=
    (** [TypAbs _ (rename_type (ext_type ρ) τ) (Rename_type (ext_type ρ) t)]
        The term "Rename_type (S Δ₁) (S Δ₂) (map (rename_type Fin.FS) Γ) (ext_type ρ) τ t" has type
        "map (rename_type (ext_type ρ)) (map (rename_type Fin.FS) Γ) ⊢ rename_type (ext_type ρ) τ"
        while it is expected to have type "map (rename_type Fin.FS) ?Γ ⊢ rename_type (ext_type ρ) τ". *)
    (** [(Λ Rename_type (ext_type ρ) t)%term]
        The term "Rename_type (S Δ₁) (S Δ₂) (map (rename_type Fin.FS) Γ) (ext_type ρ) τ t" has type
        "map (rename_type (ext_type ρ)) (map (rename_type Fin.FS) Γ) ⊢ rename_type (ext_type ρ) τ"
        while it is expected to have type "map (rename_type Fin.FS) ?Γ ⊢ ?τ". *)
    (Λ eq_rect
       (map (rename_type (ext_type ρ)) (map (rename_type Fin.FS) Γ))
       (fun Γ => Γ ⊢ rename_type (ext_type ρ) τ)
       (Rename_type (ext_type ρ) t)
       (map (rename_type Fin.FS) (map (rename_type ρ) Γ)) _)%term;
  Rename_type (Δ₁:=Δ₁) (Δ₂:=Δ₂) (Γ:=Γ) ρ (TypApp _ τ τ' t)%term :=
    (** [(Rename_type ρ t ⦗ rename_type ρ τ' ⦘)%term]
        The term "(Rename_type Δ₁ Δ₂ Γ ρ (∀ τ)%ty t ⦗ rename_type ρ τ' ⦘)%term" has type
        "map (rename_type ρ) Γ
        ⊢ @rename_type (S Δ₁) (S Δ₂) (ext_type ρ) τ `[[ rename_type ρ τ']])%ty" while it is expected to have type
        "map (rename_type ρ) Γ ⊢ rename_type ρ (τ `[[ τ']])%ty". *)
    eq_rect
      (rename_type (ext_type ρ) τ `[[ rename_type ρ τ']])%ty
      (fun τ => map (rename_type ρ) Γ ⊢ τ)
      (Rename_type ρ t ⦗ rename_type ρ τ' ⦘)%term
      (rename_type ρ (τ `[[ τ']])%ty) _.
Next Obligation. apply map_rename_typ_ext. Defined.
Next Obligation. apply annoyed. Defined.

Definition exts_Rename_type : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
    (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) -> forall τ : type (S Δ),
      Has τ (map (rename_type Fin.FS) Γ₁) ->
      map (rename_type Fin.FS) Γ₂ ⊢ τ.
Proof.
  intros Δ Γ₁ Γ₂ σ τ h.
  apply map_has in h as [τ₁ ? h]; subst.
  apply Rename_type,σ,h.
Defined.

Unset Printing Implicit.
(*Print exts_Rename_type.*)

Equations subs : forall {Δ : nat} {Γ₁ Γ₂ : list (type Δ)},
      (forall τ : type Δ, Has τ Γ₁ -> Γ₂ ⊢ τ) ->
      forall {τ : type Δ}, Γ₁ ⊢ τ -> Γ₂ ⊢ τ :=
  subs σ (Id _ _ h)     := σ _ h;
  subs σ (λ τ ⇒ t)%term := (λ τ ⇒ subs (exts σ τ) t)%term;
  subs σ (t₁ ⋅ t₂)%term := (subs σ t₁ ⋅ subs σ t₂)%term;
  subs σ (Λ t)%term     := (Λ subs (exts_Rename_type σ) t)%term;
  subs σ (t ⦗ τ ⦘)%term := (subs σ t ⦗ τ ⦘)%term.
