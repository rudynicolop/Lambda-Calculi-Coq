Require Export Lambda.PTS.Sub Coq.Classes.RelationClasses Setoid.

Open Scope term_scope.

Reserved Notation "x '⟶' y" (no associativity, at level 80).

Inductive br {S : Set} : term S -> term S -> Prop :=
| br_sub A B C :
  (λ A ⇒ B) ⋅ C ⟶ B [[ C ]]
| br_app_l A A' B :
  A ⟶ A' ->
  A ⋅ B ⟶ A' ⋅ B
| br_app_r A B B' :
  B ⟶ B' ->
  A ⋅ B ⟶ A ⋅ B'
| br_abs_l A A' B :
  A ⟶ A' ->
  λ A ⇒ B ⟶ λ A' ⇒ B
| br_abs_r A B B' :
  B ⟶ B' ->
  λ A ⇒ B ⟶ λ A ⇒ B'
| br_pi_l A A' B :
  A ⟶ A' ->
  ∏ A `, B ⟶ ∏ A' `, B
| br_pi_r A B B' :
  B ⟶ B' ->
  ∏ A `, B ⟶ ∏ A `, B'
where "x '⟶' y" := (br x y) : type_scope.

(** Reflexive-transitive closure. *)
Reserved Notation "A '⟶*' B" (at level 80, no associativity).

Inductive br_rt {sorts : Set} : term sorts -> term sorts -> Prop :=
| br_rt_refl A :
  A ⟶* A
| br_rt_trans A B C :
  A ⟶ B -> B ⟶* C -> A ⟶* C
where "A '⟶*' B" := (br_rt A B) : type_scope.

(** Reflexive-symmetric-transitive closure. *)
Reserved Notation "A '=β' B" (at level 80, no associativity).

Inductive br_rst {sorts : Set} : term sorts -> term sorts -> Prop :=
| br_br A B :
  A ⟶ B -> A =β B
| br_refl A :
  A =β A
| br_sym A B :
  A =β B -> B =β A
| br_trans A B C :
  A =β B -> B =β C -> A =β C
where "A '=β' B" := (br_rst A B) : type_scope.

Section Congruence.
  Context {sorts : Set}.
  
  Local Hint Constructors br : core.

  Lemma br_subs_context : forall (A B : term sorts) σ,
      A ⟶ B -> subs σ A ⟶ subs σ B.
  Proof.
    intros A B σ h; generalize dependent σ;
      induction h; intro σ; simpl; auto.
    rewrite subs_sub_distr; auto.
  Qed.
  
  Lemma br_sub_context : forall A B C : term sorts,
      A ⟶ B -> A [[ C ]] ⟶ B [[ C ]].
  Proof.
    eauto using br_subs_context.
  Qed.
  
  Local Hint Constructors br_rt : core.

  Lemma br_br_rt : forall A B : term sorts, A ⟶ B -> A ⟶* B.
  Proof.
    intros A B h; eauto.
  Qed.

  Lemma br_rt_transitve : forall A B C : term sorts,
      A ⟶* B -> B ⟶* C -> A ⟶* C.
  Proof.
    intros A B C hab; generalize dependent C;
      induction hab; intros C' hbc; auto.
    eapply br_rt_trans; eauto.
  Qed.

  Lemma br_rt_app_cong_l : forall A B C : term sorts,
      A ⟶* B -> A ⋅ C ⟶* B ⋅ C.
  Proof.
    intros A B C h; generalize dependent C;
      induction h; eauto.
  Qed.

  Lemma br_rt_app_cong_r : forall A B C : term sorts,
      B ⟶* C -> A ⋅ B ⟶* A ⋅ C.
  Proof.
    intros A B C h; generalize dependent A;
      induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_transitve : core.
  Local Hint Resolve br_rt_app_cong_l : core.
  Local Hint Resolve br_rt_app_cong_r : core.
  
  Lemma br_rt_app_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> A ⋅ C ⟶* B ⋅ D.
  Proof. eauto. Qed.

  Lemma br_rt_abs_cong_l : forall A B C : term sorts,
      A ⟶* B -> λ A ⇒ C ⟶* λ B ⇒ C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rt_abs_cong_r : forall A B C : term sorts,
      B ⟶* C -> λ A ⇒ B ⟶* λ A ⇒ C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_abs_cong_l : core.
  Local Hint Resolve br_rt_abs_cong_r : core.
  
  Lemma br_rt_abs_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> λ A ⇒ C ⟶* λ B ⇒ D.
  Proof. eauto. Qed.

  Lemma br_rt_pi_cong_l : forall A B C : term sorts,
      A ⟶* B -> ∏ A `, C ⟶* ∏ B `, C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rt_pi_cong_r : forall A B C : term sorts,
      B ⟶* C -> ∏ A `, B ⟶* ∏ A `, C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rt_pi_cong_l : core.
  Local Hint Resolve br_rt_pi_cong_r : core.
  
  Lemma br_rt_pi_cong : forall A B C D : term sorts,
      A ⟶* B -> C ⟶* D -> ∏ A `, C ⟶* ∏ B `, D.
  Proof. eauto. Qed.

  Local Hint Resolve br_rt_app_cong : core.
  Local Hint Resolve br_rt_abs_cong : core.
  Local Hint Resolve br_rt_pi_cong : core.
  Local Hint Resolve br_br_rt : core.

  Lemma br_mapply_rename : forall (A B : term sorts) m ρ,
      A ⟶ B -> mapply m (Rename ρ) A ⟶  mapply m (Rename ρ) B.
  Proof.
    intros A B m ρ h; generalize dependent ρ;
      generalize dependent m; induction h;
      intros m ρ.
    - rewrite mapply_Rename_app,
        mapply_Rename_abs, mapply_Rename_sub_distr; auto.
    - do 2 rewrite mapply_Rename_app; auto.
    - do 2 rewrite mapply_Rename_app; auto.
    - do 2 rewrite mapply_Rename_abs; auto.
    - do 2 rewrite mapply_Rename_abs; auto.
    - do 2 rewrite mapply_Rename_pi; auto.
    - do 2 rewrite mapply_Rename_pi; auto.
  Qed.

  Lemma br_mapply_rename_mapply_sub_helper : forall m n x (A B : term sorts),
      A ⟶ B ->
      mapply n (Rename S) (mapply m exts (sub_helper A) x)
             ⟶* mapply n (Rename S) (mapply m exts (sub_helper B) x).
  Proof.
    intro m; induction m as [| m ih];
      intros n [| x] A B h; cbn; unfold "$"; auto.
    - auto using br_mapply_rename.
    - pose proof ih (S n) x _ _ h as H; cbn in H.
      do 2 rewrite mapply_comm; assumption.
  Qed.
  
  Lemma br_mapply_sub_helper : forall x m (A B : term sorts),
      A ⟶ B ->
      mapply m exts (sub_helper A) x
             ⟶* mapply m exts (sub_helper B) x.
  Proof.
    intro x; induction x as [| x ih];
      intros [| m] A B h; cbn; unfold "$"; auto.
    pose proof br_mapply_rename_mapply_sub_helper m 1 x _ _ h;
      cbn in *; assumption.
  Qed.

  Lemma br_subs_substitute : forall (A B C : term sorts) m,
      A ⟶ B ->
      subs (mapply m exts (sub_helper A)) C
           ⟶* subs (mapply m exts (sub_helper B)) C.
  Proof.
    intros A B C; generalize dependent B;
      generalize dependent A;
      induction C as
      [s | x | C₁ ihC₁ C₂ ihC₂
      | C₁ ihC₁ C₂ ihC₂ | C₁ ihC₁ C₂ ihC₂];
      intros A B m h; cbn; eauto using br_mapply_sub_helper.
    - apply br_rt_abs_cong; eauto.
      specialize ihC₂ with A B (S m); cbn in ihC₂; auto.
    - apply br_rt_pi_cong; eauto.
      specialize ihC₂ with A B (S m); cbn in ihC₂; auto.
  Qed.
  
  Lemma br_sub_substitute : forall A B C : term sorts,
      A ⟶ B -> C [[ A ]] ⟶* C [[ B ]].
  Proof.
    intros A B C h; unfold "_ [[ _ ]]".
    pose proof br_subs_substitute A B C 0 h as H;
      cbn in H; assumption.
  Qed.
  
  Local Hint Constructors br_rst : core.

  Lemma br_rt_rst : forall A B : term sorts,
      A ⟶* B -> A =β B.
  Proof.
    intros A B h; induction h; eauto.
  Qed.
  
  Lemma br_rst_app_cong_l : forall A₁ A₂ B : term sorts,
      A₁ =β A₂ -> A₁ ⋅ B =β A₂ ⋅ B.
  Proof.
    intros A₁ A₂ B h; generalize dependent B;
      induction h; eauto.
  Qed.

  Lemma br_rst_app_cong_r : forall A B₁ B₂ : term sorts,
      B₁ =β B₂ -> A ⋅ B₁ =β A ⋅ B₂.
  Proof.
    intros A B₁ B₂ h; generalize dependent A;
      induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_app_cong_l : core.
  Local Hint Resolve br_rst_app_cong_r : core.
  
  Lemma br_rst_app_cong : forall A₁ A₂ B₁ B₂ : term sorts,
      A₁ =β A₂ -> B₁ =β B₂ -> A₁ ⋅ B₁ =β A₂ ⋅ B₂.
  Proof. eauto. Qed.

  Lemma br_rst_abs_cong_l : forall A B C : term sorts,
      A =β B -> λ A ⇒ C =β λ B ⇒ C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rst_abs_cong_r : forall A B C : term sorts,
      B =β C -> λ A ⇒ B =β λ A ⇒ C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_abs_cong_l : core.
  Local Hint Resolve br_rst_abs_cong_r : core.
  
  Lemma br_rst_abs_cong : forall A B C D : term sorts,
      A =β B -> C =β D -> λ A ⇒ C =β λ B ⇒ D.
  Proof. eauto. Qed.

  Lemma br_rst_pi_cong_l : forall A B C : term sorts,
      A =β B -> ∏ A `, C =β ∏ B `, C.
  Proof.
    intros A B C h; generalize dependent C; induction h; eauto.
  Qed.

  Lemma br_rst_pi_cong_r : forall A B C : term sorts,
      B =β C -> ∏ A `, B =β ∏ A `, C.
  Proof.
    intros A B C h; generalize dependent A; induction h; eauto.
  Qed.

  Local Hint Resolve br_rst_pi_cong_l : core.
  Local Hint Resolve br_rst_pi_cong_r : core.
  
  Lemma br_rst_pi_cong : forall A B C D : term sorts,
      A =β B -> C =β D -> ∏ A `, C =β ∏ B `, D.
  Proof. eauto. Qed.

  Lemma br_rst_reflexive : Reflexive (@br_rst sorts).
  Proof. auto. Qed.

  Lemma br_rst_symmetric : Symmetric (@br_rst sorts).
  Proof. auto. Qed.

  Lemma br_rst_transitive : Transitive (@br_rst sorts).
  Proof. eauto. Qed.
End Congruence.

Add Parametric Relation sorts
  : (term sorts)
      (@br_rst sorts)
    reflexivity proved by br_rst_reflexive
    symmetry proved by br_rst_symmetric
    transitivity proved by br_rst_transitive as br_rst_eq.

Add Parametric Morphism sorts : (@app sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as app_mor.
Proof. auto using br_rst_app_cong. Qed.

Add Parametric Morphism sorts : (@abs sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as abs_mor.
Proof. auto using br_rst_abs_cong. Qed.

Add Parametric Morphism sorts : (@pi sorts)
    with signature @br_rst sorts ==>  @br_rst sorts ==>  @br_rst sorts as pi_mor.
Proof. auto using br_rst_pi_cong. Qed.
