Require Export Lambda.PTS.Red.

Module Type Triple.
  Parameter sorts : Set.
  Parameter axiom : sorts -> sorts -> Prop.
  Parameter rule : sorts -> sorts -> sorts -> Prop.
End Triple.

Reserved Notation "Γ '⊢' A '∈' B" (no associativity, at level 80).

Module Judge (T : Triple).
  Import T.

  Inductive judge (Γ : list (term sorts)) : term sorts -> term sorts -> Prop :=
  | judge_sort s₁ s₂ :
    axiom s₁ s₂ ->
    Γ ⊢ sort s₁ ∈ sort s₂
  | judge_ident x A :
    nth_error Γ x = Some A ->
    Γ ⊢ ident x ∈ A
  | judge_app A B C a :
    Γ ⊢ C ∈ ∏ A `, B ->
    Γ ⊢ a ∈ A ->
    Γ ⊢ C ⋅ a ∈ B [[ a ]]
  | judge_pi A B s₁ s₂ s₃ :
    rule s₁ s₂ s₃ ->
    Γ ⊢ A ∈ sort s₁ ->
    map (Rename S) (A :: Γ) ⊢ B ∈ sort s₂ ->
    Γ ⊢ ∏ A `, B ∈ sort s₃
  | judge_abs A B b s₁ s₂ s₃ :
    rule s₁ s₂ s₃ ->
    Γ ⊢ A ∈ sort s₁ ->
    map (Rename S) (A :: Γ) ⊢ b ∈ B ->
    map (Rename S) (A :: Γ) ⊢ B ∈ sort s₂ ->
    Γ ⊢ λ A ⇒ b ∈ ∏ A `, B
  | judge_conv A B B' s :
    B =β B' ->
    Γ ⊢ B ∈ sort s ->
    Γ ⊢ A ∈ B ->
    Γ ⊢ A ∈ B'
  where "Γ '⊢' A '∈' B" := (judge Γ A B) : type_scope.
  
  Equations Derive Signature for judge.

  Local Hint Constructors judge : core.

  Lemma preservation : forall A A',
      A ⟶ A' -> forall Γ B, Γ ⊢ A ∈ B -> Γ ⊢ A' ∈ B.
  Proof.
    intros A A' h Γ B ht.
    generalize dependent A'.
    induction ht; intros A' hA'; inv hA'; eauto.
    - inv ht1.
      + (* lemmas :
           1. [map (Rename S) (A :: Γ) ⊢ B ∈ C -> Γ ⊢ a ∈ A -> Γ ⊢ B [[a]] ∈ C [[a]]] *) admit.
      + (* lemma. *) admit.
    - apply IHht2 in H2 as h.
      (* lemmas:
         1. [a \longrightarrow a' -> B [[ a ]] ⟶ B [[ a' ]]].
         2. [Γ ⊢ A ∈ ∏ B `, C -> exists s, map (Rename S) A :: Γ ⊢ C ∈ sort s] *)
      assert (hs: exists s, map (Rename S) (A :: Γ) ⊢ B ∈ sort s) by admit.
      destruct hs as [s hs].
      apply judge_conv with (B := B [[ B' ]]) (s := s); eauto.
      + (* maybe [A =β B] needs to be symmetric? *) admit.
      + (* by substitution lemma. *) admit.
    - econstructor; eauto; cbn in *.
      (* lemmas:
         1. [ Γ =β Γ' -> Γ ⊢ A ∈ B -> Γ' ⊢ A ∈ B ] *) admit.
    - (* needs similar lemmas to above. *)
      apply IHht1 in H3 as h.
      apply judge_conv with (B := ∏ A'0 `, B) (s := s₃); eauto.
      + assert (A =β A'0) by auto using br_br.
        rewrite H0; reflexivity.
      + econstructor; eauto; cbn in *.
        (* needs conv context lemma. *) admit.
      + econstructor; eauto; cbn in *.
        (* needs conv context lemma. *) admit. admit.
    - apply judge_conv with (B := B) (s := s); auto.
      apply IHht2. constructor.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
    - apply judge_conv with (B:=B) (s:=s); auto.
      apply IHht2. constructor. assumption.
  Admitted. 
  
  Lemma judge_abs_pi : forall Γ A B b s,
      map (Rename S) (A :: Γ) ⊢ b ∈ B ->
      Γ ⊢ ∏ A `, B ∈ s ->
      Γ ⊢ λ A ⇒ b ∈ ∏ A `, B.
  Proof.
    intros g A B b s hb hpi; depind hpi;
      try match goal with
          | h : ∏ _ `, _ = _ |- _ => inv h
          end; eauto.
  Qed.

  Lemma judge_app_arrow : forall Γ A B C a,
      Γ ⊢ C ∈ A → B ->
      Γ ⊢ a ∈ A ->
      Γ ⊢ C ⋅ a ∈ B.
  Proof.
    intros G A B C a hC ha.
    rewrite <- sub_rename_S with (B := B) (a := a); eauto.
  Qed.

  Lemma judge_Rename_ext_S : forall Γ B C,
      Γ ⊢ B ∈ C -> forall Es D,
        Es ++ Rename (add (length Es)) D
           :: map (Rename (add (length Es + 1))) Γ
           ⊢ Rename (mapply (length Es) ext S) B
           ∈ Rename (mapply (length Es) ext S) C.
  Proof.
    intros Γ B C h; induction h;
      intros Es D; cbn; unfold "$"; auto.
    - constructor. (*Search (mapply _ ext S).
      generalize dependent Γ;
        generalize dependent A;
        generalize dependent D;
        generalize dependent x.
      induction Es as [| E Es ih]; intros.
      + unfold length.
        rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S),
            map_Rename_id,nth_error_map, H; reflexivity.
      + replace (length (E :: Es)) with (1 + (length Es)) by reflexivity.
        rewrite <- Rename_add.
        do 2 rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S).
        destruct x as [| x]; cbn.
        specialize ih with 0 E A Γ.
        apply ih in H. cbn in H.*)
      admit.
    - rewrite Rename_sub_distr.
      econstructor; eauto.
    - econstructor; eauto; cbn.
      rewrite map_app.
      specialize IHh2 with
        (Es := Rename S (Rename (mapply (length Es) ext S) A)
                      :: map (Rename S) Es).
  Abort.
  
  Lemma judge_Rename_app : forall Γ B C,
      Γ ⊢ B ∈ C -> forall As Es,
        Es ++ As ++
           map (Rename (plus (length Es))) (map (Rename (plus (length As))) Γ)
           ⊢ Rename (mapply (length Es) ext (plus (length As))) B
           ∈ Rename (mapply (length Es) ext (plus (length As))) C.
  Proof.
    intros Γ B C h; induction h;
      intros As Es; cbn in *; unfold "$"; auto.
    - constructor.
      rewrite map_Rename_add. (*Print ext.*)
      (*Search (mapply _ ext).*)
      generalize dependent As.
      generalize dependent Γ.
      generalize dependent x.
      generalize dependent A.
      induction Es as [| E Es ih]; intros.
      + cbn; rewrite nth_error_app_plus,
          nth_error_map, H; reflexivity.
      + replace (length (E :: Es)) with
          (1 + length Es) by reflexivity.
        do 2 rewrite <- map_Rename_add; cbn.
        rewrite <- eta_expansion with (f := S).
        apply ih with (As:=As) in H as h.
        destruct x as [| x]; cbn.
        
  Abort.
  
  Lemma judge_Rename_app : forall Γ B C,
      Γ ⊢ B ∈ C -> forall As,
        As ++ map (Rename (plus (length As))) Γ
           ⊢ Rename (plus (length As)) B ∈ Rename (plus (length As)) C.
  Proof.
    intros Γ B C h; induction h; intro As; cbn in *; unfold "$"; auto.
    - constructor.
      rewrite nth_error_app_plus,
        nth_error_map, H; reflexivity.
    - rewrite Rename_sub_distr; econstructor; eauto.
    - econstructor; eauto; cbn.
      rewrite map_app. admit.
    - econstructor; eauto; cbn.
      rewrite map_app.
  Abort.
  
  Lemma judge_Rename_S : forall Γ E B C,
      Γ ⊢ B ∈ C ->
      E :: map (Rename S) Γ ⊢ Rename S B ∈ Rename S C.
  Proof.
    intros G E B C h; generalize dependent E;
      induction h; intro E; cbn in *; unfold "$"; auto.
    - constructor; cbn.
      rewrite nth_error_map, H; reflexivity.
    - rewrite Rename_sub_distr; cbn in IHh1.
      econstructor; eauto.
    - econstructor; eauto; cbn. admit.
    - econstructor; eauto; cbn. (*Check Rename_ext.*)
  Abort.
  
  Lemma judge_arrow : forall Γ A B s₁ s₂ s₃,
      rule s₁ s₂ s₃ ->
      Γ ⊢ A ∈ sort s₁ ->
      Γ ⊢ B ∈ sort s₂ ->
      Γ ⊢ A → B ∈ sort s₃.
  Proof.
    intros Γ A B s1 s2 s3 hr hA hB.
    econstructor; eauto; cbn.
  Abort.
End Judge.
