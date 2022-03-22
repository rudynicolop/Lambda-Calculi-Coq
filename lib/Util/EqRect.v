From Equations Require Export Equations.

Equations eq_rect_zwei : forall {A B : Set} {x y : A} {u v : B} {T : A -> B -> Set},
    x = y -> u = v -> T x u -> T y v :=
  eq_rect_zwei eq_refl eq_refl t := t.

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
