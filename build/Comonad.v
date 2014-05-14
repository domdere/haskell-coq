Require Import Function.
Require Import Functor.

Class Comonad (W : Type -> Type) := {

    is_functor :> Functor W;

    (* algebra *)

    counit : forall {A : Type}, W A -> A;
    duplicate : forall {A : Type}, W A -> W (W A);

    (* Comonad Laws *)
    counit_left_identity
    : forall (A : Type) (w : W A)
    , counit (duplicate w) = w;


    counit_right_identity
    : forall (A : Type) (w : W A)
    , fmap counit (duplicate w) = w;

    duplicate_squared
    : forall (A : Type) (w : W A)
    , duplicate (duplicate w) = (fmap duplicate) (duplicate w)

}.
