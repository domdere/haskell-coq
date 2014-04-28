Require Import Applicative.
Require Import Function.
Require Import Functor.

Reserved Notation "m >>= f" (at level 50).

Class Monad (M: Type -> Type) := {
    (* Must be an applicative functor *)
    monads_are_applicative :> Applicative M;

    (* functions *)
    join : forall {A : Type}, M (M A) -> M A
        where "m >>= f" := (join (fmap f m));

    (* Monad Laws *)

    monad_unit_left_identity
        : forall (A B : Type) (f : A -> M B) (x : A)
        , f x = join (fmap f (unit x));

    monad_unit_right_identity
        : forall (A : Type) (m : M A)
        , m = join (fmap unit m);

    monad_join_fmap_associative
        : forall (A : Type) (m : M (M (M A)))
        , join (join m) = join (fmap join m);

    (*This should somehow follow from associativity of join, but i cant seem to prove it*)
    bind_associative
        : forall (A B C : Type) (m : M A) (k : A -> M B) (h : B -> M C)
        , m >>= (compose join (compose (fmap h) k)) = (m >>= k) >>= h
}.

Theorem monad_unit_left_identity_1
    : forall (M : Type -> Type) (A : Type) (m : M A) (monad_dict : Monad M)
    , m = join (unit m).
Proof.
    intros.
    assert (id m = join (fmap id (unit m))).
    apply monad_unit_left_identity.
    rewrite -> functor_id_law in H.
    unfold id in H.
    assumption.
Qed.

Definition bind {M : Type -> Type} {ismonad : Monad M} {A B : Type} (m : M A) (f : A -> M B) : M B :=
    join (fmap f m).

Notation "m >>= f" := (bind m f) (at level 50).

