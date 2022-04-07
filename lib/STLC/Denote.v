Require Export Lambda.STLC.Has.

Reserved Notation "'`⟦' τ '⟧'"
         (at level 20, no associativity).

Fixpoint denote_type (τ : type) : Set :=
  match τ with
  | ⊥%ty => Empty_set
  | (τ₁ → τ₂)%ty => (`⟦τ₁⟧ -> `⟦τ₂⟧)%ty
  end
where "'`⟦' τ '⟧'" := (denote_type τ) : ty_scope.

Inductive hlist {A : Set} (F : A -> Set) : list A -> Set :=
| hnil : hlist F []
| hcons : forall a l,
    F a ->
    hlist F l ->
    hlist F (a :: l).

Check hnil.
Arguments hnil {_} {_}.
Check hnil.
Check hcons.
Arguments hcons {_} {_} {_} {_}.
Check hcons.

Example types : list type :=
  [(⊥ → ⊥)%ty; (⊥ → ⊥ → ⊥)%ty; ((⊥ → ⊥) → ⊥ → ⊥)%ty].

Check map denote_type types : list Set.
Eval cbn in map denote_type types.
Check
  hcons
  (F:=denote_type)
  (a:=(⊥ → ⊥)%ty)
  (fun x : Empty_set => x)
  (hcons
     (F:=denote_type)
     (a:=(⊥ → ⊥ → ⊥)%ty)
     (fun x y : Empty_set => x)
         (hcons
            (F:=denote_type)
            (a:=((⊥ → ⊥) → ⊥ → ⊥)%ty)
            (fun (f : Empty_set -> Empty_set) (x : Empty_set) => f x) hnil))
  : hlist denote_type types.

Reserved Notation "'⟦' t '⟧'"
         (at level 20, no associativity).

Print Has.

Equations lookup_term : forall {Γ : list type} {τ : type},
    hlist denote_type Γ -> Has τ Γ -> `⟦ τ ⟧ :=
  lookup_term (hcons v _) HasO      := v;
  lookup_term (hcons _ ϵ) (HasS hs) := lookup_term ϵ hs.

Equations denote_term : forall {Γ : list type} {τ : type},
    hlist denote_type Γ -> Γ ⊢ τ -> `⟦ τ ⟧ :=
  denote_term ϵ (Id _ _ hs)    := lookup_term ϵ hs;
  denote_term ϵ (λ τ ⇒ t)%term := fun x : `⟦ τ ⟧ => denote_term (hcons x ϵ) t;
  denote_term ϵ (t₁ ⋅ t₂)%term := (denote_term ϵ t₁) (denote_term ϵ t₂)
where "⟦ t ⟧" := (denote_term t) : term_scope.
