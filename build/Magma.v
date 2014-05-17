Class Magma (A : Type) := {
    (** A Magma is just a Set/Type with a binary operation *)

    mplus : A -> A -> A
}.

Notation "a <+> b" := (mplus a b) (at level 70).
