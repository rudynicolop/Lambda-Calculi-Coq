Require Export Lambda.Util.Basic.
From Equations Require Export Equations.

(** * List helpers. *)

Section List.
  Context {A : Type}.

  Inductive Has : A -> list A -> Type :=
  | HasO : forall a t, Has a (a :: t)
  | HasS : forall a h t, Has a t -> Has a (h :: t).

  Global Arguments HasO {_} {_}.
  Global Arguments HasS {_} {_} {_}.
  
  Equations Derive NoConfusion NoConfusionHom Subterm for list.
  Equations Derive Signature NoConfusion for Has.

  Inductive hlist (F : A -> Type) : list A -> Type :=
  | hnil : hlist F []
  | hcons : forall a l,
      F a ->
      hlist F l ->
      hlist F (a :: l).
  Equations Derive Signature NoConfusion NoConfusionHom for hlist.
  
  Global Arguments hnil {_}.
  Global Arguments hcons {_} {_} {_}.
  
  Equations lookup_has : forall {F : A -> Type} {Γ : list A} {a : A},
      hlist F Γ -> Has a Γ -> F a :=
    lookup_has (hcons v _) HasO      := v;
    lookup_has (hcons _ ϵ) (HasS hs) := lookup_has ϵ hs.
  
  Equations ext_has : forall {Γ Δ},
      (forall a : A, Has a Γ -> Has a Δ) ->
      forall b a : A, Has a (b :: Γ) -> Has a (b :: Δ) :=
    ext_has ρ _ _ HasO := HasO;
    ext_has ρ _ _ (HasS h) := HasS (ρ _ h).

  Equations ext_has_app_l : forall {Γ Δ},
      (forall a : A, Has a Γ -> Has a Δ) ->
      forall (l : list A) (a : A), Has a (l ++ Γ) -> Has a (l ++ Δ) :=
    ext_has_app_l ρ []:= ρ;
    ext_has_app_l ρ (h :: t) := ext_has (ext_has_app_l ρ t) h.
  
  Definition Has_nth_error : forall {Γ a},
      Has a Γ -> { n | nth_error Γ n = Some a}.
  Proof.
    intros l a h; induction h.
    - refine (exist _ 0 _); reflexivity.
    - destruct IHh as [k Hk].
      refine (exist _ (S k) _); assumption.
  Defined.
  
  Variant zilch : list A -> Prop := zilch_nil : zilch [].
  
  Definition lookup :
    forall {Γ : list A} {n : nat},
      n < length Γ -> A.
  Proof.
    refine
      (fix F Γ n HnΓ :=
         match Γ as Γ' return Γ = Γ' -> A with
         | []
           => fun HΓΓ' => _
         | a :: Δ
         => fun HΓΓ' =>
             match n as n' return n = n' -> A with
             | O   => fun _ => a
             | S k => fun Hnn' => F Δ k _
             end eq_refl
         end eq_refl).
    - inv HΓΓ'; cbn in *; lia.
    - subst; cbn in *; lia.
  Defined.
  
  (* Require Import Extraction.
     Recursive Extraction lookup. *)

  Definition length_nth_error' :
    forall {l : list A} {n : nat},
      n < length l -> { a | nth_error l n = Some a }.
  Proof.
    refine
    (fix F l n Hnl :=
       match
         l as l'
         return
         l = l' -> { a | nth_error l n = Some a } with
       | [] => fun H => _
       | h :: t
         => fun H =>
             match
               n as n'
               return
               n = n' -> { a | nth_error l n = Some a } with
             | O
               => fun _ => @exist _ _ h _
             | S k
               => fun Hnn' =>
                   match F t k _ with
                   | exist _ a' Hk => @exist _ _ a' _
                   end
             end eq_refl
       end eq_refl); subst; cbn in *;
      lia || reflexivity || assumption.
  Defined.

  Definition nth_error_lookup :
    forall {Γ : list A} {n : nat} (H : n < length Γ),
      nth_error Γ n = Some (lookup H).
  Proof.
    intro l; induction l as [| a l IHl];
      intros [| n] H; cbn in *;
        try lia; eauto using Lt.lt_S_n.
  Defined.

  Local Hint Constructors Has : core.
  
  Definition nth_error_Has : forall {Γ a n},
      nth_error Γ n = Some a -> Has a Γ.
  Proof.
    intro l; induction l as [| h t IHt];
      intros a [| n] Hnth; cbn in *; try discriminate; eauto.
    inv Hnth; auto.
  Defined.

  Definition nth_error_Has' : forall {Γ a},
      {n | nth_error Γ n = Some a} -> Has a Γ.
  Proof.
    intros l a [n H]; exact (nth_error_Has H).
  Defined.
  
  Definition ext_nth_error : forall {Γ Δ : list A},
      (forall a, {n | nth_error Γ n = Some a} ->
              {k | nth_error Δ k = Some a}) ->
      forall b a, {n | nth_error (b :: Γ) n = Some a} ->
               {k | nth_error (b :: Δ) k = Some a}.
  Proof.
    intros l d f b a Hab.
    apply Has_nth_error.
    apply nth_error_Has' in Hab.
    pose proof (fun a H => nth_error_Has' (f a (Has_nth_error H))) as H.
    eauto using ext_has.
  Defined.
End List.

Equations has_map :
  forall {A B : Type} (f : A -> B) {l : list A} {e : A},
    Has e l -> Has (f e) (map f l) :=
  has_map f  HasO     := HasO;
  has_map f (HasS hs) := HasS (has_map f hs).

Definition map_has : forall (A B : Type) (f : A -> B) (l : list A) b,
    Has b (map f l) -> {a : A & f a = b & Has a l}.
Proof.
  intros A B f l.
  induction l as [| a l ih]; intros b h; cbn in *; depelim h.
  - exact (existT2 _ _ a eq_refl HasO).
  - apply ih in h0 as [a' fab hasa].
    exact (existT2 _ _ a' fab (HasS hasa)).
Defined.
