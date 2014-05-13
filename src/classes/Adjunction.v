Require Import Function.
Require Import Functor.

Class Adjunction (L R : Type -> Type) := {
    left_functor :> Functor L;
    right_functor :> Functor R;

    (** Adjoints *)
    leftAdjoint : forall {A B : Type}, (L A -> B) -> A -> R B;

    rightAdjoint : forall {A B : Type}, (A -> R B) -> L A -> B;

    (** Laws/Properties *)

    (** Adjoint Isomorphism *)

    adjoint_bijection_1
        : forall {A B : Type} (g : A -> R B) (a : A)
        , (leftAdjoint (rightAdjoint g)) a = g a;

    adjoint_bijection_2
        : forall {A B : Type} (f : L A -> B) (la : L A)
        , (rightAdjoint (leftAdjoint f)) la = f la;

    (** Adjoint Naturality *)

    adjoint_natural_1
        : forall {A B C : Type} (f : L A -> B) (k : B -> C) (a : A)
        , (leftAdjoint (compose k f)) a = fmap k (leftAdjoint f a);

    adjoint_natural_2
        : forall {A B C : Type} (f : L B -> C) (h : A -> B) (a : A)
        , (leftAdjoint (compose f (fmap h))) a = (leftAdjoint f (h a));

    adjoint_natural_3
        : forall {A B C : Type} (g : B -> R C) (h : A -> B) (la : L A)
        , (rightAdjoint (compose g h)) la = (rightAdjoint g (fmap h la));

    adjoint_natural_4
        : forall {A B C : Type} (g : A -> R B) (k : B -> C) (la : L A)
        , rightAdjoint (compose (fmap k) g) la = k (rightAdjoint g la)
}.

(* unit, counit, join and duplicate *)

Definition adjoint_unit {F G : Type -> Type} {adjunction : Adjunction F G} {A : Type} : A -> G (F A) :=
    leftAdjoint id.

Definition adjoint_counit {F G : Type -> Type} {adjunction : Adjunction F G} {B : Type} : F (G B) -> B :=
    rightAdjoint id.

Definition adjoint_join {F G : Type -> Type} {adjunction : Adjunction F G} {A : Type} : G (F (G (F A))) -> G (F A) :=
    fmap adjoint_counit.

Definition adjoint_duplicate {F G : Type -> Type} {adjunction : Adjunction F G} {A : Type} : F (G A) -> F (G (F (G A))) :=
    fmap adjoint_unit.

(* Theorems *)

Theorem adjoint_bijection_1_pointfree
        : forall (F G : Type -> Type) (A B : Type) (adjunction : Adjunction F G) (g : A -> G B)
        , (leftAdjoint (rightAdjoint g)) = g.
Proof.
    intros.
    assert (forall (x : A), leftAdjoint (rightAdjoint g) x = g x).
    intros.
    apply adjoint_bijection_1.
    apply extensional_equality in H.
    assumption.
Qed.

Theorem adjoint_bijection_2_pointfree
        : forall (F G : Type -> Type) (adjunction : Adjunction F G) (A B : Type) (f : F A -> B)
        , (rightAdjoint (leftAdjoint f)) = f.
Proof.
    intros.
    assert (forall (fa : F A), rightAdjoint (leftAdjoint f) fa = f fa).
    intros.
    apply adjoint_bijection_2.
    apply extensional_equality in H.
    assumption.
Qed.

Theorem adjoint_natural_1_pointfree
        : forall (F G : Type -> Type) (A B C : Type) (adjunction : Adjunction F G) (f : F A -> B) (k : B -> C)
        , (leftAdjoint (compose k f)) = compose (fmap k) (leftAdjoint f).
Proof.
    intros.
    apply extensional_equality.
    intros.
    apply adjoint_natural_1.
Qed.

Theorem adjoint_natural_2_pointfree
    : forall (F G : Type -> Type) (A B C : Type) (adjunction : Adjunction F G) (f : F B -> C) (h : A -> B)
    , (leftAdjoint (compose f (fmap h))) = compose (leftAdjoint f) h.
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold compose at 2.
    apply adjoint_natural_2.
Qed.

Theorem adjoint_natural_3_pointfree
    : forall (F G : Type -> Type) (A B C : Type) (adjunction : Adjunction F G) (g : B -> G C) (h : A -> B)
    , (rightAdjoint (compose g h)) = compose (rightAdjoint g) (fmap h).
Proof.
    intros.
    apply extensional_equality.
    unfold compose at 2.
    intros.
    apply adjoint_natural_3.
Qed.

Theorem adjoint_natural_4_pointfree
    : forall (F G : Type -> Type) (A B C : Type) (adjunction : Adjunction F G) (g : A -> G B) (k : B -> C)
    , rightAdjoint (compose (fmap k) g) = compose k (rightAdjoint g).
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold compose at 2.
    apply adjoint_natural_4.
Qed.

Theorem adjoint_unit_left_identity
    : forall (F G : Type -> Type) (A : Type) (adjunction : Adjunction F G)
    , compose adjoint_join adjoint_unit = @id (G (F A)).
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold id.
    unfold compose.
    unfold adjoint_join.
    unfold adjoint_unit.
    unfold adjoint_counit.
    rewrite <- adjoint_natural_1.
    rewrite -> compose_right_identity.
    rewrite -> adjoint_bijection_1.
    unfold id.
    reflexivity.
Qed.

Theorem adjoint_unit_right_identity
    : forall (F G : Type -> Type) (A : Type) (adjunction : Adjunction F G)
    , compose adjoint_join (fmap (fmap adjoint_unit)) = @id (G (F A)).
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold id.
    unfold compose.
    unfold adjoint_join.
    rewrite -> functors_preserve_composition.
    unfold adjoint_counit.
    unfold adjoint_unit.
    rewrite <- adjoint_natural_3_pointfree.
    rewrite -> compose_left_identity.
    rewrite -> adjoint_bijection_2_pointfree.
    rewrite -> functor_id_law.
    unfold id.
    reflexivity.
Qed.

Lemma adjoint_counit_squared
    : forall (F G : Type -> Type) (A : Type) (adjunction : Adjunction F G)
    , compose adjoint_counit adjoint_counit = compose adjoint_counit (fmap (@adjoint_join F G adjunction A)).
Proof.
    intros.
    apply extensional_equality.
    unfold adjoint_counit at 3.
    unfold compose at 2.
    intros.
    rewrite <- adjoint_natural_3.
    rewrite -> compose_left_identity.
    unfold compose.
    unfold adjoint_counit at 2.
    assert (rightAdjoint (compose (fmap adjoint_counit) id) x = adjoint_counit (rightAdjoint id x)).
    apply adjoint_natural_4.
    rewrite <- H.
    rewrite -> compose_right_identity.
    unfold adjoint_join.
    reflexivity.
Qed.

Theorem adjoint_join_associative
    : forall (F G : Type -> Type) (A : Type) (adjunction : Adjunction F G)
    , compose adjoint_join (@adjoint_join F G adjunction (G (F A))) = compose adjoint_join ((compose fmap fmap) adjoint_join).
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold compose.
    unfold adjoint_join at 3.
    rewrite -> functors_preserve_composition.
    unfold adjoint_join at 1.
    unfold adjoint_join at 1.
    rewrite -> functors_preserve_composition.
    rewrite -> adjoint_counit_squared.
    reflexivity.
Qed.
