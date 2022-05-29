Require Export Lambda.Util.Basic.
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

Lemma mapply_ext : forall m ρ X,
    ext (mapply m ext ρ) (mapply m ext S X) = mapply m ext S (mapply m ext ρ X).
Proof.
  intro m; induction m as [| m ih]; intros ρ X; cbn.
  - reflexivity.
  - destruct X as [| X]; cbn; auto.
Qed.

Lemma mapply_rename_typ_ext : forall (τ : typ) (ρ : nat -> nat) (m : nat),
    rename_typ (mapply (S m) ext ρ) (rename_typ (mapply m ext S) τ)
    = rename_typ (mapply m ext S) (rename_typ (mapply m ext ρ) τ).
Proof.
  intro τ; induction τ as [X | τ ih | τ₁ ih₁ τ₂ ih₂];
    intros ρ m; cbn.
  - rewrite mapply_ext; reflexivity.
  - f_equal; specialize ih with ρ (S m); cbn in ih.
    rewrite ih; reflexivity.
  - f_equal; eauto.
Qed.

Lemma rename_typ_ext : forall (τ : typ) (*[(Δ₁ Δ₂ : nat)]*) (ρ : nat -> nat),
    (*[(forall Y : nat, Y < Δ₁ -> ρ Y < Δ₂) ->] *)
    rename_typ (ext ρ) (rename_typ S τ) = rename_typ S (rename_typ ρ τ).
Proof.
  intros τ ρ; pose proof mapply_rename_typ_ext τ ρ 0 as h.
  cbn in h; assumption.
Qed.

Lemma map_rename_typ_ext : forall (*[(Δ₁ Δ₂ : nat)]*) (ρ : nat -> nat) (Γ : list typ),
    (*[(forall Y : nat, Y < Δ₁ -> ρ Y < Δ₂) ->]*)
    map (rename_typ (ext ρ)) (map (rename_typ S) Γ)
    = map (rename_typ S) (map (rename_typ ρ) Γ).
Proof.
  intros ρ Γ; induction Γ as [| τ Γ ih];
    cbn; f_equal; auto using rename_typ_ext.
Qed.
  
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

Lemma mapply_exts_typ : forall (m X : nat) (ρ : nat -> nat) (τ : typ),
    mapply m exts_typ (sub_typ_helper (rename_typ ρ τ)) (ext (mapply m ext ρ) X)
    = rename_typ (mapply m ext ρ) (mapply m exts_typ (sub_typ_helper τ) X).
Proof.
  intro m; induction m as [| m ih]; intros X ρ τ; cbn.
  - destruct X as [| X]; cbn; reflexivity.
  - destruct X as [| X]; cbn; try reflexivity.
    rewrite ih with (ρ:=ρ),rename_typ_ext; reflexivity.
Qed.

Lemma mapply_subs_typ_exts_typ : forall (τ τ' : typ) (ρ : nat -> nat) (m : nat),
    subs_typ
      (mapply m exts_typ (sub_typ_helper (rename_typ ρ τ')))
      (rename_typ (mapply (S m) ext ρ) τ)
    = rename_typ
        (mapply m ext ρ)
        (subs_typ (mapply m exts_typ (sub_typ_helper τ')) τ).
Proof.
  intro τ; induction τ as [X | τ ih | τ₁ ih₁ τ₂ ih₂];
    intros τ' ρ m; cbn.
  - rewrite mapply_exts_typ; reflexivity.
  - f_equal. specialize ih with (m:=S m); cbn in ih.
    rewrite ih; reflexivity.
  - f_equal; eauto.
Qed.
        
Lemma rename_typ_sub_typ : forall (τ τ' : typ) (ρ : nat -> nat),
    (rename_typ (ext ρ) τ `[[ rename_typ ρ τ']])%typ
    = rename_typ ρ (τ `[[ τ']])%typ.
Proof.
  unfold "_ `[[ _ ]]".
  intros τ τ' ρ.
  pose proof mapply_subs_typ_exts_typ τ τ' ρ 0 as h; cbn in h.
  assumption.
Qed.

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

Record tenv : Set := { dpth:nat; typs:list typ }.

Definition push (τ : typ) '({| dpth:=Δ; typs:=Γ |} : tenv) : tenv :=
  {| dpth:=Δ; typs:=τ::Γ |}.

Definition rename_tenv '({| dpth:=Δ; typs:=Γ |} : tenv) : tenv :=
  {| dpth:=S Δ; typs:=map (rename_typ S) Γ |}.

Coercion dpth : tenv >-> nat.

Inductive trm_typ (Γ : tenv) : trm -> typ -> Prop :=
| Id_typ x τ :
  nth_error (typs Γ) x = Some τ ->
  Γ ⊢ x ∈ τ
| Abs_typ τ τ' t :
  Γ ⊢ok τ ->
  push τ Γ ⊢ t ∈ τ' ->
  Γ ⊢ (λ τ ⇒ t)%trm ∈ (τ → τ')%typ
| App_typ τ τ' t₁ t₂ :
  Γ ⊢ t₁ ∈ (τ → τ')%typ ->
  Γ ⊢ t₂ ∈  τ ->
  Γ ⊢ (t₁ ⋅ t₂)%trm ∈ τ'
| TypAbs_typ τ t :
  rename_tenv Γ ⊢ t ∈ τ ->
  Γ ⊢ (Λ t)%trm ∈ (∀ τ)%typ
| TypApp_typ τ τ' t :
  Γ ⊢ok τ' ->
  Γ ⊢ t ∈ (∀ τ)%typ ->
  Γ ⊢ (t ⦗τ'⦘)%trm ∈ (τ `[[τ']])%typ
where "x ⊢ y ∈ z" := (trm_typ x y z) : type_scope.

Local Hint Constructors trm_typ : core.

Lemma trm_typ_ok : forall Γ t τ,
    Γ ⊢ t ∈ τ ->
    Forall (ok_typ Γ) (typs Γ) ->
    Γ ⊢ok τ.
Proof.
  intros Γ t τ h hΓ.
  induction h as
    [ Γ X τ hX
    | Γ τ t hok h ih
    | Γ τ τ' t₁ t₂ h₁ ih₁ h₂ ih₂
    | Γ τ t h ih
    | Γ τ τ' t hok h ih ]; cbn in *.
  - rewrite Forall_forall in hΓ.
    eauto using nth_error_In.
  - destruct Γ as [Δ Γ]; cbn in *; auto.
  - pose proof ih₁ hΓ as ih; inv ih; assumption.
  - destruct Γ as [Δ Γ]; cbn in *.
    constructor. apply ih.
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

Lemma ext_typs : forall (Γ₁ Γ₂ : list typ) (ρ : nat -> nat),
    (forall y τ', nth_error Γ₁ y     = Some τ' ->
             nth_error Γ₂ (ρ y) = Some τ') ->
    forall x τ τ', nth_error (τ :: Γ₁) x = Some τ' ->
              nth_error (τ :: Γ₂) (ext ρ x) = Some τ'.
Proof.
  intros Γ₁ Γ₂ ρ hρ [| X] τ τ' h; cbn in *; auto.
Qed.

Local Hint Resolve ext_typs : core.

Lemma nth_error_map_ex : forall (U V : Set) (f : U -> V) l n v,
      nth_error (map f l) n = Some v ->
      exists u, f u = v /\ nth_error l n = Some u.
Proof.
  intros U V f l.
  induction l as [| u' l IHl];
    intros [| n] v h; cbn in *; try discriminate; eauto.
  inv h; eauto.
Qed.

Lemma rename_typ_ext_typs : forall (Γ₁ Γ₂ : list typ) (ρ : nat -> nat),
    (forall y τ', nth_error Γ₁ y = Some τ' -> nth_error Γ₂ (ρ y) = Some τ') ->
    forall x τ,
      nth_error (map (rename_typ S) Γ₁) x = Some τ ->
      nth_error (map (rename_typ S) Γ₂) (ρ x) = Some τ.
Proof.
  intros Γ₁ Γ₂ ρ hρ x rτ h.
  apply nth_error_map_ex in h as (τ & ? & h); subst.
  auto using map_nth_error.
Qed.

Local Hint Resolve rename_typ_ext_typs : core.

Lemma rename_trm_typs :
  forall (Δ : nat) (Γ₁ Γ₂ : list typ)
    (ρ : nat -> nat) (t : trm) (τ : typ),
    (forall y τ', nth_error Γ₁ y = Some τ' ->
             nth_error Γ₂ (ρ y) = Some τ') ->
    {| dpth:=Δ; typs:=Γ₁ |} ⊢ t ∈ τ ->
    {| dpth:=Δ; typs:=Γ₂ |} ⊢ rename_trm ρ t ∈ τ.
Proof.
  intros Δ Γ₁ Γ₂ ρ t τ hρ h.
  generalize dependent ρ.
  generalize dependent Γ₂.
  remember {| dpth:=Δ; typs:=Γ₁ |} as ΔΓ₁ eqn:eqΓ₁.
  generalize dependent Γ₁.
  generalize dependent Δ.
  induction h as
    [ Γ X τ hX
    | Γ τ τ' t hok h ih
    | Γ τ τ' t₁ t₂ h₁ ih₁ h₂ ih₂
    | Γ τ t h ih
    | Γ τ τ' t hok h ih ]; cbn in *;
    intros Δ Γ₁ eq Γ₂ ρ hρ; subst; cbn in *; eauto.
Qed.

Local Hint Resolve rename_trm_typs : core.

Definition exts_trm (σ : nat -> trm) (x : nat) : trm :=
  match x with
  | O   => O
  | S n => rename_trm S (σ n)
  end.

Lemma exts_trm_typs : forall (Δ : nat) (Γ₁ Γ₂ : list typ) (σ : nat -> trm),
    (forall y τ', nth_error Γ₁ y = Some τ' ->
             {| dpth:=Δ; typs:=Γ₂ |} ⊢ σ y ∈ τ') ->
    forall x τ τ', nth_error (τ :: Γ₁) x = Some τ' ->
              {| dpth:=Δ; typs:=τ::Γ₂ |} ⊢ exts_trm σ x ∈ τ'.
Proof.
  intros Δ Γ₁ Γ₂ σ hσ [| x] τ τ' h; cbn in *; eauto.
Qed.

Local Hint Resolve exts_trm_typs : core.

Fixpoint rename_typ_trm (ρ : nat -> nat) (t : trm) : trm :=
  match t with
  | Id x => Id x
  | (λ τ ⇒ t)%trm => (λ rename_typ ρ τ ⇒ rename_typ_trm ρ t)%trm
  | (t₁ ⋅ t₂)%trm => (rename_typ_trm ρ t₁ ⋅ rename_typ_trm ρ t₂)%trm
  | (Λ t)%trm     => (Λ rename_typ_trm (ext ρ) t)%trm
  | (t ⦗τ⦘)%trm   => (rename_typ_trm ρ t ⦗rename_typ ρ τ⦘)%trm
  end.

Lemma rename_typ_trm_typs : forall (Δ₁ Δ₂ : nat) (Γ : list typ) (ρ : nat -> nat),
    (forall Y, Y < Δ₁ -> ρ Y < Δ₂) ->
    forall t τ, {| dpth:=Δ₁; typs:=Γ |} ⊢ t ∈ τ ->
           {| dpth:=Δ₂; typs:=map (rename_typ ρ) Γ |}
             ⊢ rename_typ_trm ρ t ∈ rename_typ ρ τ.
Proof.
  intros Δ₁ Δ₂ Γ ρ hρ t τ h.
  generalize dependent ρ.
  generalize dependent Δ₂.
  remember {| dpth := Δ₁; typs := Γ |} as Δ₁Γ eqn:eqΔ₁Γ.
  generalize dependent Γ.
  generalize dependent Δ₁.
  induction h as
    [ Δ₁Γ X τ hX
    | Δ₁Γ τ τ' t hok h ih
    | Δ₁Γ τ τ' t₁ t₂ h₁ ih₁ h₂ ih₂
    | Δ₁Γ τ t h ih
    | Δ₁Γ τ τ' t hok h ih ]; cbn in *;
    intros Δ₁ Γ eq Δ₂ ρ hρ; subst;
    cbn in *; eauto using map_nth_error.
  - constructor; cbn; eauto.
    specialize ih with (Γ:=τ :: Γ); cbn in ih; eauto.
  - constructor; cbn.
    pose proof ih _ _ eq_refl _ (ext ρ) (fun X => ext_ok _ _ _ X hρ) as IH.
    assert (help:
             map (rename_typ (ext ρ)) (map (rename_typ S) Γ)
             = map (rename_typ S) (map (rename_typ ρ) Γ))
      by auto using map_rename_typ_ext.
    rewrite help in IH; assumption.
  - pose proof ih _ _ eq_refl _ _ hρ as IH.
    apply TypApp_typ with (τ':=rename_typ ρ τ') in IH; eauto.
    assert (help:
             (rename_typ (ext ρ) τ `[[ rename_typ ρ τ']])%typ
             = rename_typ ρ (τ `[[ τ']])%typ)
      by auto using rename_typ_sub_typ.
    rewrite help in IH; assumption.
Qed.

(* Print Assumptions rename_typ_trm_typs.
   [Closed under the global context]! *)

Definition exts_rename_typ_trm (σ : nat -> trm) (X : nat) : trm :=
  rename_typ_trm S (σ X).

Fixpoint subs_trm (σ : nat -> trm) (t : trm) : trm :=
  match t with
  | Id x          => σ x
  | (λ τ ⇒ t)%trm => (λ τ ⇒ subs_trm (exts_trm σ) t)%trm
  | (t₁ ⋅ t₂)%trm => (subs_trm σ t₁ ⋅ subs_trm σ t₂)%trm
  | (Λ t)%trm     => (Λ subs_trm (exts_rename_typ_trm σ) t)%trm
  | (t ⦗τ⦘)%trm   => (subs_trm σ t ⦗τ⦘)%trm
  end.
