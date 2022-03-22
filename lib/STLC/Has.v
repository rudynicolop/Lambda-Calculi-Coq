From Lambda Require Export ListUtil STLC.SimpleTypes.

(** Inspired by
    Programming Language Foundations in Agda. *)

(** De Bruijn syntax. *)

Reserved Notation "Γ '⊢' τ" (at level 80, no associativity).

Inductive term : list type -> type -> Set :=
| Id (Γ : list type) (τ : type) :
  Has τ Γ ->
  Γ ⊢ τ
| Abs (Γ : list type) (τ τ' : type) :
  τ :: Γ ⊢ τ' ->
  Γ ⊢ τ → τ'
| App (Γ : list type) (τ τ' : type) :
  Γ ⊢ τ → τ' ->
  Γ ⊢ τ ->
  Γ ⊢ τ'
where "Γ '⊢' τ" := (term Γ τ) : type_scope.

Equations Derive Signature NoConfusion NoConfusionHom Subterm for term.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "'`λ' t"
  := (Abs _ _ _ t)
       (at level 15, right associativity) : term_scope.
Notation "'λ' τ '⇒' t"
  := (Abs _ τ _ t)
       (at level 15, right associativity) : term_scope.
Notation "'λ' τ '↣' .. '↣' ρ '⇒' t"
  := (Abs _ τ _ .. (Abs _ ρ _ t) ..)
       (at level 15, right associativity) : term_scope.
Notation "x '⋅' y"
  := (App _ _ _ x y)
       (at level 14, left associativity) : term_scope.

Equations
  Rename
  {Γ Δ} :
  (forall τ, Has τ Γ -> Has τ Δ) -> forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
  Rename f (Id _ _ h)   := Id _ _ (f _ h);
  Rename f (λ ρ ⇒ t')%term := (`λ Rename (ext_has f ρ) t')%term;
  Rename f (t₁ ⋅ t₂)%term  := (Rename f t₁ ⋅ Rename f t₂)%term.

Equations Exts : forall {Γ Δ},
    (forall τ, Has τ Γ -> Δ ⊢ τ) ->
    forall ρ σ, Has σ (ρ :: Γ) -> ρ :: Δ ⊢ σ :=
  Exts f _ _ HasO := Id _ _ HasO;
  Exts f _ _ (HasS hs) := Rename (fun τ => @HasS _ τ _ _) (f _ hs).

Equations Exts_app_l : forall {Γ Δ},
    (forall τ, Has τ Γ -> Δ ⊢ τ) ->
    forall τs τ, Has τ (τs ++ Γ) -> (τs ++ Δ) ⊢ τ :=
  Exts_app_l σ [] := σ;
  Exts_app_l σ (α :: τs) := Exts (Exts_app_l σ τs) α.

Equations
  subs : forall {Γ Δ},
    (forall {τ}, Has τ Γ -> Δ ⊢ τ) ->
    forall {σ}, Γ ⊢ σ -> Δ ⊢ σ :=
  subs f (Id _ _ h)   := f _ h;
  subs f (λ ρ ⇒ t')%term := (`λ subs (Exts f ρ) t')%term;
  subs f (t₁ ⋅ t₂)%term  := (subs f t₁ ⋅ subs f t₂)%term.

Equations sub_helper : forall {Γ τ}, Γ ⊢ τ -> forall τ', Has τ' (τ :: Γ) -> Γ ⊢ τ' :=
  sub_helper t _ HasO := t;
  sub_helper _ _ (HasS hs) := Id _ _ hs.

Definition sub {Γ τ τ'} (body : τ :: Γ ⊢ τ') (arg : Γ ⊢ τ) : Γ ⊢ τ' :=
    subs (sub_helper arg) body.

Notation "x '[[' y ']]'"
  := (sub x y) (at level 12, no associativity) : term_scope.

Reserved Notation "x '-->' y" (at level 80, no associativity).

Inductive bred {Γ} : forall {τ}, Γ ⊢ τ -> Γ ⊢ τ -> Prop :=
| bred_bred τ τ' (t₁ : τ :: Γ ⊢ τ') t₂ :
    ((`λ t₁) ⋅ t₂)%term --> (t₁ [[ t₂ ]])%term
| bred_abs τ τ' (t t' : τ :: Γ ⊢ τ') :
    t -->  t' ->
    (`λ t)%term --> (`λ t')%term
| bred_app_l τ τ' (t₁ t₁' : Γ ⊢ τ → τ') t₂ :
    t₁ -->  t₁' ->
    (t₁ ⋅ t₂)%term -->  (t₁' ⋅ t₂)%term
| bred_app_r τ τ' (t₁ : Γ ⊢ τ → τ') t₂ t₂' :
    t₂ -->  t₂' ->
    (t₁ ⋅ t₂)%term -->  (t₁ ⋅ t₂')%term
where "x '-->' y" := (bred x y) : type_scope.
Derive Signature for bred.

Print Assumptions bred.

Local Hint Constructors bred : core.

Variant value {Γ : list type} : forall {τ : type}, Γ ⊢ τ -> Prop :=
  Abs_value (τ τ' : type) (t : τ :: Γ ⊢ τ') : value (`λ t)%term.
Derive Signature for value.

Print Assumptions value.

Lemma canonical_forms_abs : forall {τ τ' : type} (t : [] ⊢ (τ → τ')%ty),
    value t -> exists body : [τ] ⊢ τ', t = (`λ body)%term.
Proof.
  intros τ τ' t v.
  depelim v; eauto.
Qed.

Print Assumptions canonical_forms_abs.

Local Hint Constructors bred : core.
Local Hint Constructors value : core.

Theorem Progress : forall {τ} (t : [] ⊢ τ), value t \/ exists t', t --> t'.
Proof.
  intros τ t; depind t; eauto.
  - inv h.
  - clear IHt2.
    destruct IHt1 as [v1 | (t1' & ih1)]; eauto.
    apply canonical_forms_abs in v1 as [t1' ?]; subst; eauto.
Qed.

Print Assumptions Progress.

Lemma bred_exm : forall {Γ τ} (t : Γ ⊢ τ),
    (exists t', t --> t') \/ forall t', ~ (t --> t').
Proof.
  intros Γ τ t; depind t; eauto.
  - right; intros t' H; inv H.
  - destruct IHt as [(t' & ih) | ih]; eauto.
    right; intros t' H; depelim H.
    apply ih in H; contradiction.
  - destruct IHt1 as [(t1' & ih1) | ih1]; eauto.
    destruct IHt2 as [(t2' & ih2) | ih2]; eauto.
    depelim t1; eauto.
    + right; intros t' H. depelim H.
      * depelim H.
      * apply ih2 in H; contradiction.
    + right; intros t' H. depelim H.
      * apply ih1 in H; contradiction.
      * apply ih2 in H; contradiction.
Qed.

Notation "e '-->*' e'"
  := (refl_trans_closure bred e e')
       (at level 40, no associativity).

(** Termination predicate. *)
Definition halts {Γ τ} (t : Γ ⊢ τ) : Prop :=
  exists t', t -->* t' /\ forall t'', ~ (t' -->  t'').

(** Strongly Normalizing. *)
Definition SN {Γ τ} : Γ ⊢ τ -> Prop := Acc (fun t' t => t -->  t').
Equations Derive Signature for Acc.

Section HaltsSN.
  Local Hint Constructors refl_trans_closure : core.
  
  Lemma SN_halts : forall {Γ τ} (t : Γ ⊢ τ), SN t -> halts t.
  Proof.
    intros Γ τ t Hsn; unfold halts; depind Hsn.
    destruct (bred_exm x) as [(t & Ht) | Ht]; eauto.
    apply H0 in Ht as Ht_. destruct Ht_ as (t' & Ht' & Ht''); eauto.
  Qed.
End HaltsSN.

Lemma subs_subs_distr :
  forall {Γ Δ} (σ : forall τ, Has τ Γ -> Δ ⊢ τ)
    τs {τ τ'} (t : (τs ++ τ :: Γ) ⊢ τ') (t' : Γ ⊢ τ),
    subs
      (Exts_app_l σ τs)
      (subs (Exts_app_l (sub_helper t') τs) t)
    = subs
        (Exts_app_l (sub_helper (subs σ t')) τs)
        (eq_rect
           _ (fun Γ => Γ ⊢ τ')
           (subs
              (Exts_app_l σ (τs ++ [τ]))
              (eq_rect
                 _ (fun Γ => Γ ⊢ τ')
                 t _ (app_assoc _ [τ] _)))
           _ (eq_sym (app_assoc _ _ _))).
Proof.
  intros Γ Δ σ τs τ τ' t t'.
  depind t.
  - rewrite subs_equation_1. admit.
  - do 2 rewrite subs_equation_2.
    pose proof IHt _ _ σ (τ :: τs) _ _ _ eq_refl t' as ih; clear IHt.
    do 2 rewrite Exts_app_l_equation_2 in ih.
    cbn in *; rewrite ih; clear ih.
Admitted.

Lemma subs_sub_distr :
  forall {Γ Δ} (σ : forall τ, Has τ Γ -> Δ ⊢ τ)
    {τ τ'} (t₁ : τ :: Γ ⊢ τ') (t₂ : Γ ⊢ τ),
    subs σ (t₁ [[t₂]])%term = (subs (Exts σ τ) t₁ [[subs σ t₂]])%term.
Proof.
  intros Γ Δ σ τ τ' t t'.
  unfold "_ [[ _ ]]".
  depind t.
  - do 2 rewrite subs_equation_1.
    depelim h.
    + rewrite Exts_equation_1,subs_equation_1.
      do 2 rewrite sub_helper_equation_1; reflexivity.
    + rewrite Exts_equation_2,sub_helper_equation_2,
        subs_equation_1. admit.
  - do 4 rewrite subs_equation_2; f_equal.
    admit (** Look to [SF/Dep.v]. *).
  - do 4 rewrite subs_equation_3; f_equal; auto.
Admitted.

Lemma subs_bred : forall {Γ τ} (t t' : Γ ⊢ τ),
    t -->  t' -> forall {Δ} (σ : forall τ, Has τ Γ -> Δ ⊢ τ),
      subs σ t --> subs σ t'.
Proof.
  intros Γ τ t t' br; depind br; intros Δ σ.
  - rewrite subs_equation_3,subs_equation_2.
    assert (H:subs σ (t₁ [[t₂]])%term
              = (subs (Exts σ τ) t₁ [[subs σ t₂]])%term)
      by auto using subs_sub_distr.
    rewrite H; auto.
  - do 2 rewrite subs_equation_2; auto.
  - do 2 rewrite subs_equation_3; auto.
  - do 2 rewrite subs_equation_3; auto.
Qed.

Lemma sub_bred : forall {Γ τ τ'} (bdy bdy' : τ :: Γ ⊢ τ'),
    bdy --> bdy' -> forall (t : Γ ⊢ τ),
    (bdy [[ t ]])%term --> (bdy' [[ t ]])%term.
Proof.
  eauto using subs_bred.
Qed.
