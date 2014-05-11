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
        : forall {A B : Type} (g : A -> R B) (a : A), (leftAdjoint (rightAdjoint g)) a = g a;

    adjoint_bijection_2
        : forall {A B : Type} (f : L A -> B) (la : L A), (rightAdjoint (leftAdjoint f)) la = f la


}.
