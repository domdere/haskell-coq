Require Import Function.

Class Functor (functor: Type -> Type) := {
    fmap: forall {A B : Type}, (A -> B) -> functor A -> functor B;

    functors_preserve_composition
        : forall (A B C: Type)
        , forall (g : B -> C)
        , forall (f : A -> B)
        , forall (c : functor A)
        , fmap g (fmap f c) = fmap (compose g f) c;

    functor_id_law
        : forall (A : Type), forall (c : functor A), fmap id c = id c
}.


