Require Import Magma.

Class Semigroup (A : Type) := {

    (** A semigroup is a Magma *)
    is_magma :> Magma A;

    (** Associativity law: The binary operation must be associative *)
    semigroup_associativity
        : forall (x y z : A)
        , (x <+> (y <+> z)) = ((x <+> y) <+> z)

}.

