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
  Local Hint Constructors br : core.
  Local Hint Constructors br_rt : core.
  Local Hint Constructors br_rst : core.

  Context {sorts : Set}.
  
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
