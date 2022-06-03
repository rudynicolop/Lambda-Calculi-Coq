Require Export Lambda.PTS.Typing.

(** System U definitions from
    [https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf]. *)

Module SystemU_Spec.
  Inductive U_sorts : Set := prop | type | triangle.

  Declare Scope U_sort_scope.
  Delimit Scope U_sort_scope with sort.
  Notation "'*'" := prop (at level 0, no associativity).
  Notation "'◻'" := type (at level 0, no associativity).
  Notation "'△'" := triangle (at level 0, no associativity).
  Open Scope U_sort_scope.
  
  Variant U_axiom : U_sorts -> U_sorts -> Prop :=
    | axiom_prop : U_axiom * ◻
    | axiom_type : U_axiom ◻ △.

  Variant U_rule : U_sorts -> U_sorts -> U_sorts -> Prop :=
    | prop_prop : U_rule * * *
    | type_prop : U_rule ◻ * *
    | type_type : U_rule ◻ ◻ ◻
    | triangle_prop : U_rule △ * *
    | triangle_type : U_rule △ ◻ ◻.

  Local Hint Constructors U_rule : core.
  
  Lemma U_rule_star : forall s, U_rule s * *.
  Proof.
    intros []; auto.
  Qed.
End SystemU_Spec.

Module SystemU_Triple <: Triple.
  Include SystemU_Spec.
  Definition sorts := U_sorts.
  Definition axiom := U_axiom.
  Definition rule := U_rule.
End SystemU_Triple.

Module SystemU.
  Export SystemU_Triple.
  Include Judge SystemU_Triple.

  Definition pow (A : term sorts) := A → sort *.

  Lemma Rename_pow : forall A ρ,
      Rename ρ (pow A) = pow (Rename ρ A).
  Proof.
    intros A ρ; reflexivity.
  Qed.
  
  Notation "'⊥'" := (∏ sort * `, ident 0) (at level 0, no associativity) : term_scope.
  Notation "'¬' A" := (A → ⊥) (at level 41) : term_scope.
  
  Lemma Rename_false : forall ρ, Rename ρ ⊥ = ⊥.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Lemma Rename_neg : forall ρ A, Rename ρ (¬ A) = ¬ Rename ρ A.
  Proof.
    intros ρ A; reflexivity.
  Qed.
  
  Definition U :=
    ∏ sort ◻ `, (pow (pow (ident 0)) → ident 0) → (pow (pow (ident 0))).

  Lemma Rename_U : forall ρ,
      Rename ρ U = U.
  Proof.
    intro ρ; reflexivity.
  Qed.
  
  Local Hint Constructors U_axiom : core.
  Local Hint Constructors U_rule : core.
  Local Hint Constructors judge : core.
  Local Hint Resolve judge_abs_pi : core.
  Local Hint Resolve judge_app_arrow : core.
  Local Hint Unfold axiom : core.
  Local Hint Unfold rule : core.
  Local Hint Unfold pow : core.
  Local Hint Rewrite map_cons : core.
  Local Hint Rewrite (@Rename_arrow sorts) : core.
  Local Hint Resolve U_rule_star : core.

  Lemma pow_judge : forall Γ A,
      Γ ⊢ A ∈ sort ◻ -> Γ ⊢ pow A ∈ sort ◻.
  Proof.
    intros Γ A h;
      econstructor; try eassumption; eauto;
      autorewrite with core; cbn; auto.
  Qed.

  Lemma false_judge : forall Γ, Γ ⊢ ⊥ ∈ sort *.
  Proof.
    intro Γ; eapply judge_pi with (s₁ := ◻); eauto.
  Qed.
  
  Local Hint Resolve false_judge : core.

  Lemma neg_judge : forall Γ A s, Γ ⊢ A ∈ sort s -> Γ ⊢ ¬ A ∈ sort *.
  Proof.
    intros Γ A s h;
      eapply judge_pi with (s₁ := s); eauto.
  Qed.

  Local Hint Resolve neg_judge : core.
  Local Hint Resolve pow_judge : core.
  Arguments pow : simpl never.
  
  Lemma U_judge : forall Γ, Γ ⊢ U ∈ sort ◻.
  Proof.
    intros Γ; unfold U; simpl; unfold "$".
    eapply judge_pi with (s₁ := △) (s₂ := ◻);
      eauto; autorewrite with core.
    eapply judge_pi with (s₁ := ◻) (s₂ := ◻); eauto; simpl; unfold "$".
    - eapply judge_pi with (s₁ := ◻) (s₂ := ◻); cbn; unfold "$"; eauto.
    - do 2 (eapply judge_pi with (s₁ := ◻) (s₂ := ◻); cbv; eauto).
  Qed.

  Local Hint Resolve U_judge : core.
  
  Definition τ :=
    λ pow (pow U) ⇒
      λ sort ◻ ⇒
      λ (pow (pow (ident 0)) → ident 0) ⇒
      λ pow (ident 1) ⇒
      ident 3 ⋅ λ U ⇒ (ident 1 ⋅ (ident 2 ⋅ (ident 0 ⋅ ident 3 ⋅ ident 2))).
   
  Lemma Rename_τ : forall ρ, Rename ρ τ = τ.
  Proof.
    intros ρ; reflexivity.
  Qed.
  
  Arguments U : simpl never.
  Local Hint Rewrite Rename_pow : core.
  Local Hint Rewrite Rename_U : core.
  
  Lemma τ_judge : forall Γ, Γ ⊢ τ ∈ pow (pow U) → U.
  Proof.
    intro Γ; unfold τ.
    apply judge_abs_pi with (s := sort ◻); autorewrite with core.
    - apply judge_abs_pi with (s := sort ◻); auto.
      autorewrite with core. unfold Rename at 1.
      apply judge_abs_pi with (s := sort ◻); autorewrite with core; eauto.
      + unfold Rename at 1; unfold Rename at 2; unfold "$".
        apply judge_abs_pi with (s := sort ◻);
          autorewrite with core.
        * do 2 unfold Rename at 2; unfold "$".
          unfold Rename at 1; unfold "$".
          unfold Rename at 2; unfold "$".
          unfold Rename at 3; unfold "$".
          unfold Rename at 2; unfold "$".
          unfold Rename at 6; unfold "$".
          eapply judge_app_arrow.
          -- constructor; reflexivity.
          -- apply judge_abs_pi with (s := sort ◻);
               autorewrite with core.
             ++ do 2 unfold Rename at 1; unfold "$".
                do 2 unfold Rename at 2; unfold "$".
                unfold Rename at 7; unfold "$".
                do 3 (eapply judge_app_arrow;
                      try (econstructor; reflexivity)).
                replace ((pow (pow (ident 3)) → ident 3) → (pow (pow (ident 3))))
                  with (((pow (pow (ident 0)) → ident 0) → (pow (pow (ident 0)))) [[ ident 3 ]])
                  by reflexivity.
                eapply judge_app; econstructor; reflexivity.
             ++ eapply judge_pi with (s₁ := ◻); eauto;
                  autorewrite with core; cbn; auto.
        * unfold Rename at 2 6. unfold "$".
          do 2 (eapply judge_pi with (s₁ := ◻); eauto;
                autorewrite with core; cbn; auto; unfold "$").
      + unfold Rename at 4; unfold "$".
        repeat (eapply judge_pi with (s₁ := ◻); eauto;
                autorewrite with core; try (cbn; auto; assumption)).
        cbn; constructor; reflexivity.
    - apply judge_pi with (s₁ := ◻) (s₂ := ◻); auto.
  Qed.

  Definition σ := λ U ⇒ ident 0 ⋅ U ⋅ τ.

  Lemma Rename_σ : forall ρ, Rename ρ σ = σ.
  Proof.
    intro ρ; reflexivity.
  Qed.
  
  Arguments τ : simpl never.
  Local Hint Resolve τ_judge : core.

  Lemma σ_judge : forall Γ, Γ ⊢ σ ∈ U → pow (pow U).
  Proof.
    intro Γ; unfold σ.
    apply judge_abs_pi with (s := sort ◻); auto;
      autorewrite with core.
    eapply judge_app_arrow; eauto.
    - replace ((pow (pow U) → U) → pow (pow U)) with
        (((pow (pow (ident 0)) → ident 0) → pow (pow (ident 0))) [[ U ]])
        by reflexivity.
      econstructor; eauto.
      constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻); eauto;
        autorewrite with core; try (cbn; auto; assumption).
  Qed.

  Definition Δ :=
    λ U ⇒ ¬ (∏ pow U `, σ ⋅ ident 1 ⋅ ident 0 → ident 0 ⋅ (τ ⋅ (σ ⋅ ident 1))).

  Lemma Rename_Δ : forall ρ, Rename ρ Δ = Δ.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Arguments σ : simpl never.
  Local Hint Resolve σ_judge : core.

  Lemma Δ_judge : forall Γ, Γ ⊢ Δ ∈ pow U.
  Proof.
    intro Γ; unfold Δ.
    apply judge_abs_pi with (s := sort ◻);
      autorewrite with core.
    - unfold Rename at 4.
      eapply neg_judge.
      do 2 (econstructor; eauto; autorewrite with core).
      + eapply judge_app_arrow.
        * eapply judge_app_arrow; eauto.
          -- apply σ_judge.
          -- constructor; reflexivity.
        * constructor; reflexivity.
      + cbn; unfold "$".
        eapply judge_app_arrow; eauto.
        constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻); eauto;
        autorewrite with core; cbn; auto.
  Qed.

  Definition Ω :=
    τ ⋅ λ pow U ⇒ ∏ U `, σ ⋅ ident 0 ⋅ ident 1 → ident 1 ⋅ ident 0.

  Lemma Rename_Ω : forall ρ, Rename ρ Ω = Ω.
  Proof.
    intro ρ; reflexivity.
  Qed.

  Lemma Ω_judge : forall Γ, Γ ⊢ Ω ∈ U.
  Proof.
    intro Γ; unfold Ω.
    eapply judge_app_arrow; eauto.
    eapply judge_abs_pi; eauto; autorewrite with core.
    - cbn; econstructor; eauto; unfold "$";
        autorewrite with core.
      econstructor; eauto; autorewrite with core.
      + eapply judge_app_arrow.
        * eapply judge_app_arrow.
          -- apply σ_judge.
          -- constructor; reflexivity.
        * constructor; reflexivity.
      + eapply judge_app_arrow; autorewrite with core;
          constructor; reflexivity.
    - eapply judge_pi with (s₁ := ◻) (s₃ := ◻); eauto;
        autorewrite with core; cbn; auto.
  Qed.
  
  Arguments Δ : simpl never.
  Arguments Ω : simpl never.

  Definition bad :=
    λ (∏ pow U `, ∏ U `, (σ ⋅ ident 1 ⋅ ident 0 → ident 1 ⋅ ident 0) → ident 1 ⋅ Ω) ⇒
      ((ident 0 ⋅ Δ ⋅
              λ U ⇒ λ σ ⋅ ident 0 ⋅ Δ ⇒
              λ (∏ pow U `, σ ⋅ ident 2 ⋅ ident 0 → ident 0 ⋅ (τ ⋅ (σ ⋅ ident 2))) ⇒
              ident 0 ⋅ Δ ⋅ ident 1 ⋅ λ pow U ⇒ ident 0 ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)))
         ⋅ λ pow U ⇒ ident 1 ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)))
      ⋅ λ pow U ⇒ λ (∏ U `, σ ⋅ ident 0 ⋅ ident 1 → ident 1 ⋅ ident 0) ⇒
      ident 0 ⋅ Ω ⋅ λ U ⇒ ident 1 ⋅ (τ ⋅ (σ ⋅ ident 0)).

  Lemma bad_judge : forall Γ, Γ ⊢ bad ∈ ⊥.
  Proof.
    intro Γ; unfold bad.
    Fail apply judge_abs_pi.
    (* How does [bad] have type [⊥]?
       Makes no sense... *)
  Abort.
End SystemU.

Definition leibniz {A : Set} (x y : A) : Prop := forall P : A -> Prop, P x <-> P y.

Lemma eq_leibniz : forall {A : Set} (a : A), leibniz a a.
Proof.
  firstorder.
Qed.

Lemma leibniz_eq : forall {A : Set} (x y : A), leibniz x y -> x = y.
Proof.
  unfold leibniz.
  intros A x y h.
  specialize h with (eq x).
  destruct h as [h _]; auto.
Qed.
