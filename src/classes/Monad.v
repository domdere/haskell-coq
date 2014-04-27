Require Import Applicative.
Require Import Function.
Require Import Functor.

Class Monad (M: Type -> Type) := {
    (* Must be an applicative functor *)
    monads_are_applicative :> Applicative M;

    (* functions *)
    join : forall {A : Type}, M (M A) -> M A;

    (* Monad Laws *)

    monad_unit_left_identity
        : forall (A B : Type) (f : A -> M B) (x : A)
        , f x = join (fmap f (unit x));

    monad_unit_right_identity
        : forall (A : Type) (m : M A)
        , m = join (fmap unit m);

    monad_join_fmap_associative
        : forall (A B C : Type) (m : M A) (k : A -> M B) (h : B -> M C)
        , join (fmap (fun x : A => join (fmap h (k x))) m) = join (fmap h (join (fmap k m)))

}.

Definition bind {M : Type -> Type} {ismonad : Monad M} {A B : Type} (m : M A) (f : A -> M B) : M B :=
    join (fmap f m).

Notation "m >>= f" := (bind m f) (at level 50).

Theorem bind_associative
    : forall (A B C : Type) (M : Type -> Type) (monad_dict : Monad M) (m : M A) (k : A -> M B) (h : B -> M C)
    , m >>= (fun (x : A) => (k x >>= h)) = (m >>= k) >>= h.
Proof.
    intros.
    unfold bind.
    apply monad_join_fmap_associative.
Qed.

