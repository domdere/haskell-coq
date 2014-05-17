Require Import Magma.
Require Import Semigroup.

Class Monoid (A : Type) := {

    (** A Monoid is a Semigroup *)
    is_semigroup :> Semigroup A;

    (** There's a special element/value that satisfies the below laws *)
    midentity : A;

    (** Monoid laws *)

    (** midentity is a left identity for the binary operation *)
    monoid_left_identity
        : forall (a : A)
        , (midentity <+> a) = a;

    (** midentity is a right identity for the binary operation *)
    monoid_right_identity
        : forall (a : A)
        , (a <+> midentity) = a

}.

