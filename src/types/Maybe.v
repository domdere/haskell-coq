Require Import Applicative.
Require Import Function.
Require Import Functor.
Require Import Monad.

Inductive maybe (A : Type) : Type :=
    | nothing   : maybe A
    | just      : A -> maybe A.

Definition maybeMap {A B : Type} (f : A -> B) (mx : maybe A) : maybe B :=
    match mx with
        | nothing   => nothing B
        | just x    => just B (f x)
    end.

Definition maybeJoin {A : Type} (mmx : maybe (maybe A)) : maybe A :=
    match mmx with
        | nothing => nothing A
        | just mx => mx
    end.

Definition maybeBind {A B : Type} (mx : maybe A) (f : A -> maybe B) : maybe B := maybeJoin (maybeMap f mx).

Definition maybeLiftM2 {A B C : Type} (f : A -> B -> C) (ma : maybe A) (mb : maybe B) : maybe C :=
    maybeBind ma (fun (a : A) => maybeBind mb (fun (b : B) => just C (f a b))).

Definition maybeApply {A B : Type} : (maybe (A -> B)) -> maybe A -> maybe B := maybeLiftM2 id.

Instance maybe_functor : Functor maybe := {
    fmap := @maybeMap
}.
Proof.
-
    intros.
    unfold compose.
    unfold maybeMap.
    destruct c as [| a].
        reflexivity.

        reflexivity.

-
    intros.
    unfold maybeMap.
    destruct c as [| a].
        unfold id.
        reflexivity.

        unfold id.
        reflexivity.
Defined.

Instance maybe_applicative : Applicative maybe := {
    unit := just;
    apply := @maybeApply
}.
Proof.
-
 intros.
 unfold maybeApply.
 unfold maybeLiftM2.
 unfold maybeBind.
 unfold maybeJoin.
 destruct x as [| x'].
  unfold maybeMap.
  reflexivity.

  unfold maybeMap.
  unfold id.
  reflexivity.

-
    intros.
    unfold maybeApply.
    unfold maybeLiftM2.
    unfold maybeBind.
    unfold maybeJoin.
    destruct w as [| w'].
    unfold maybeMap.
    destruct u as [| uf].
    reflexivity.

    destruct v as [| vf].
        reflexivity.

        reflexivity.

    unfold maybeMap.
    destruct u as [| uf].
    reflexivity.

    destruct v as [| vf].
        reflexivity.

        unfold id.
        unfold compose.
        reflexivity.

-
    intros.
    unfold maybeApply.
    unfold maybeLiftM2.
    unfold maybeBind.
    unfold maybeJoin.
    unfold id.
    unfold maybeMap.
    reflexivity.

-
    intros.
    unfold maybeApply.
    unfold maybeLiftM2.
    unfold id.
    unfold maybeBind.
    unfold maybeJoin.
    destruct u as [| uf].
        unfold maybeMap.
        reflexivity.

        unfold maybeMap.
        reflexivity.

-
    intros.
    unfold fmap.
    unfold maybe_functor.
    unfold maybeApply.
    unfold maybeLiftM2.
    unfold maybeBind.
    unfold maybeJoin.
    destruct x as [| x'].
        unfold maybeMap.
        reflexivity.

        unfold maybeMap.
        unfold id.
        reflexivity.
Defined.

Instance maybe_monad : Monad maybe := {
    join := @maybeJoin
}.
Proof.
-
    intros.
    unfold unit.
    unfold maybe_applicative.
    unfold fmap.
    unfold is_functor.
    unfold maybe_functor.
    unfold maybeMap.
    unfold maybeJoin.
    reflexivity.

-
    intros.
    unfold id.
    unfold fmap.
    unfold is_functor.
    unfold maybe_applicative.
    unfold maybe_functor.
    destruct m as [| a].
        unfold unit.
        unfold maybeMap.
        unfold maybeJoin.
        reflexivity.

        unfold maybeMap.
        unfold unit.
        unfold maybeJoin.
        reflexivity.

-
    intros.
    unfold fmap.
    unfold is_functor.
    unfold maybe_applicative.
    unfold maybe_functor.
    unfold maybeMap.
    destruct m as [| mma].
        unfold maybeJoin.
        reflexivity.

        unfold maybeJoin.
        destruct mma as [| ma].
            reflexivity.

            reflexivity.

-
    intros.
    destruct m as [| a].
        unfold fmap.
        unfold is_functor.
        unfold maybe_applicative.
        unfold maybe_functor.
        unfold maybeMap.
        unfold maybeJoin.
        reflexivity.

        unfold fmap.
        unfold is_functor.
        unfold maybe_applicative.
        unfold maybe_functor.
        unfold maybeMap.
        unfold compose.
        destruct (k a) as [| ka].
            unfold maybeJoin.
            reflexivity.

            unfold maybeJoin.
            reflexivity.

Defined.
