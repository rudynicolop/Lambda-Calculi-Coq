Require Export Lambda.STLC.Dep.

Module Examples.
  Open Scope term_scope.
  
  Example _identity_func : [] ⊢ ⊥ → ⊥ := λ ⊥ ⇒ # 0.
  Compute _identity_func.

  Example _nat : type := (⊥ → ⊥) → ⊥ → ⊥.
  Local Hint Unfold _nat : core.

  Example _zero : [] ⊢ _nat := λ ⊥ → ⊥ ⇒ λ ⊥ ⇒ # 0.
  Example _zero' : [] ⊢ _nat := `λ `λ # 0.
  Example _zero'' : [] ⊢ _nat := λ ⊥ → ⊥ ↣ ⊥ ⇒ # 0.

  Example _one : [] ⊢ _nat.
  Proof.
    refine (λ ⊥ → ⊥ ↣ ⊥ ⇒ ID 1 _ ⋅ ID 0 _); reflexivity.
  Defined.

  Fail Example _one' : [] ⊢ _nat := ∫ ∫ ID 1 _ `⋅ ID 0 _.

  Example _succ : [] ⊢ _nat → _nat.
  Proof.
    refine (λ _nat ⇒ λ ⊥ → ⊥ ↣ ⊥ ⇒ ID 1 _ ⋅ (ID 2 _ ⋅ ID 1 _ ⋅ ID 0 _)); reflexivity.
  Defined.

  Example _two : [] ⊢ _nat.
  Proof.
    refine (`λ `λ ID 1 _ ⋅ (ID 1 _ ⋅ ID 0 _)); reflexivity.
  Defined.

  Compute _succ ⋅ _zero.
End Examples.
