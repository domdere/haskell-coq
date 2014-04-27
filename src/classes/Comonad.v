Require Import Function.
Require Import Functor.

Class Comonad (W : Type -> Type) := {

    is_functor :> Functor W;

    (* algebra *)

    counit : forall {A : Type}, W A -> A;
    duplicate : forall {A : Type}, W A -> W (W A);

    (* Comonad Laws *)
    counit_left_inverse
    : forall (A : Type) (w : W A)
    , (compose counit duplicate) w = w;


    counit_right_inverse
    : forall (A : Type) (w : W A)
    , (compose (fmap counit) duplicate) w = w;

    duplicate_squared
    : forall (A : Type) (w : W A)
    , (compose duplicate duplicate) w = (compose (fmap duplicate) duplicate) w

}.
