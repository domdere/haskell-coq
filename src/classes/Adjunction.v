Require Import Function.
Require Import Functor.

Class Adjunction (L R : Type -> Type) := {
    left_functor :> Functor L;
    right_functor :> Functor R;

    (* adjoints *)
    leftAdjoint : forall {A B : Type}, (L A -> B) -> A -> R B;

    rightAdjoint : forall {A B : Type}, (A -> R B) -> L A -> B;

    (* laws/properties *)

    adjoint_bijection_1
        : forall {A B : Type} (g : A -> R B) (a : A)
        , (leftAdjoint (rightAdjoint g)) a = g a;

    adjoint_bijection_2
        : forall {A B : Type} (f : L A -> B) (la : L A)
        , (rightAdjoint (leftAdjoint f)) la = f la;

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
