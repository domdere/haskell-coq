Require Import Applicative.
Require Import Function.
Require Import Functor.

Reserved Notation "m >>= f" (at level 50).

Class Monad (M: Type -> Type) := {
    (** Must be an applicative functor *)
    monads_are_applicative :> Applicative M;

    (** Functions *)
    join : forall {A : Type}, M (M A) -> M A
        where "m >>= f" := (join (fmap f m));

    (** Monad Laws *)

    monad_unit_left_identity
        : forall (A B : Type) (f : A -> M B) (x : A)
        , f x = join (fmap f (unit x));

    monad_unit_right_identity
        : forall (A : Type) (m : M A)
        , m = join (fmap unit m);

    monad_join_fmap_associative
        : forall (A : Type) (m : M (M (M A)))
        , join (join m) = join (fmap join m);

    (** Not sure if this property should result from the other 3 directly...
        I'm having trouble proving it in the general case...
    *)
    monad_join_pullback
        : forall (A B : Type) (f : A -> M B) (mma : M (M A))
        , join (fmap (fmap f) mma) = fmap f (join mma);

    (** The join function should behave consistently with the Applicatives apply function,
        The functor is supposed to characterise the behaviour of a "context",
        The Applicative and Monad instances should both reflect the same behaviour,
        If the behaviour differs, then the type should separated into 2.  One with
        the Applicative behaviour (which may or may not have a Monad behaviour to extend it) and
        another with the Monad behaviour (which will determine its Applicative behaviour
        with monadApply defined below.)
    *)
    bind_apply_consistent
        : forall (A B : Type) (mf : M (A -> B)) (ma : M A)
        , apply mf ma = join (fmap (fun (f : A -> B) => fmap f ma) mf)
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

(*
Lemma bind_associative_lemma_1
    : forall (M : Type -> Type) (A B : Type) (monad : Monad M) (f : A -> M B) (mma : M (M A))
    , join (fmap (fmap f) mma) = fmap f (join mma).
Proof.
    intros.
    rewrite -> monad_join_fmap_associative.
    rewrite -> functors_preserve_composition.
    rewrite -> functors_preserve_composition.
Qed.
*)

(*
WIP: I want to remove this from from the Monad laws if i can prove it from the
Applicative/Monad/Functor laws...

Lemma bind_associative_lemma_1
    : forall (M : Type -> Type) (A B : Type) (monad : Monad M) (f : A -> M B) (mma : M (M A))
    , join (fmap (fmap f) mma) = fmap f (join mma).
Proof.
    intros.
    assert (fmap f (join mma) = (unit f) <*> (join mma)).
    rewrite -> bind_apply_consistent.
    rewrite <- monad_unit_left_identity.
    reflexivity.
    (*rewrite -> H.*)
    (*rewrite -> unit_fmap.
    rewrite <- fmap_unit.*)
    rewrite -> monad_unit_right_identity.
    rewrite -> functors_preserve_composition.

    rewrite -> bind_apply_consistent.
    rewrite <- monad_unit_left_identity.
Qed.
*)

Theorem bind_associative
    : forall (M : Type -> Type) (monad : Monad M) (A B C : Type) (m : M A) (k : A -> M B) (h : B -> M C)
    , m >>= (compose join (compose (fmap h) k)) = (m >>= k) >>= h.
Proof.
    intros.
    unfold bind.
    assert (join (fmap k m) = (compose join (fmap k)) m).

    unfold compose.
    reflexivity.
    rewrite -> H.
    rewrite <- functors_preserve_composition.
    rewrite <- monad_join_fmap_associative.
    rewrite <- functors_preserve_composition.
    unfold compose.
    rewrite -> monad_join_pullback.
    reflexivity.
Qed.

(** This chain forces you to define your Applicative instance before the Monad instance,
    and Monad instances are sometimes (read: Almost Always) easier to define than Applicative instances, this lets you go
    in that direction, just pass in the functions that are going to become your unit and bind
    and it will give you a function for your Applicative apply function that will satisfy
    the applicative laws (provided the unit and bind obey the Monad laws).
*)

Definition monadLift2 {M : Type -> Type} {A B C : Type} (unit' : C -> M C) (bind1 : M A -> (A -> M C) -> M C) (bind2 : M B -> (B ->  M C) -> M C) (f : A -> B -> C) (m1 : M A) (m2 : M B) : M C :=
    bind1 m1 (fun (a : A) => bind2 m2 (fun (b : B) => unit' (f a b))).

Definition monadApply {M : Type -> Type} {A B : Type} (unit' : B -> M B) (bind1 : M (A -> B) -> ((A -> B) -> M B) -> M B) (bind2 : M A -> (A -> M B) -> M B) : M (A -> B) -> M A -> M B :=
    monadLift2 unit' bind1 bind2 id.
