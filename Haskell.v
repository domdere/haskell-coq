Definition id {A : Type} (a : A) : A := a.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B): A -> C :=
    fun a : A => g (f a).

Class Functor (functor: Type -> Type) := {
    fmap: forall {A B : Type}, (A -> B) -> functor A -> functor B;

    functors_preserve_composition
        : forall (A B C: Type)
        , forall (g : B -> C)
        , forall (f : A -> B)
        , forall (c : functor A)
        , (compose (fmap g) (fmap f)) c = fmap (compose g f) c;

    functor_id_law
        : forall (A : Type), forall (c : functor A), fmap id c = id c
}.

Class Applicative (F: Type -> Type) := {
    (* It must also be a functor *)
    is_functor :> Functor F;

    (* functions *)
    unit : forall {A : Type}, A -> F A;
    apply : forall {A B : Type}, F (A -> B) -> F A -> F B;


    (* laws *)
    unit_identity
        : forall (A : Type) (x : F A), apply (unit id) x = x;

    unit_compose
        : forall (A B C : Type) (u : F (B -> C)) (v : F (A -> B)) (w : F A)
        , apply (apply (apply (unit compose) u) v) w = apply u (apply v w);

    unit_homomorphism
        : forall (A B : Type) (f : A -> B) (x : A)
        , apply (unit f) (unit x) = unit (f x);

    unit_interchange
        : forall (A B : Type) (u : F (A -> B)) (x : A)
        , apply u (unit x) = apply (unit (fun (f : A -> B) => f x)) u;

    unit_fmap
        : forall (A B : Type) (f : A -> B) (x : F A)
        , fmap f x = apply (unit f) x
}.

Notation "v <*> w" := (apply v w) (at level 50).

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
        , id m = join (fmap unit m);

    (* monad_join_associative
        : forall (A : Type) (m : M (M (M A)))
        , join m = fmap join m *)

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


Inductive myMaybe (A : Type) : Type :=
    | empty : myMaybe A
    | just : A -> myMaybe A.

Definition maybeMap {A B : Type} (f : A -> B) (m : @myMaybe A) : @myMaybe B :=
    match m with
        | empty => empty B
        | just x => just B (f x)
    end.

Definition applyMaybe {A B : Type} (mf : @myMaybe (A -> B)) (m : @myMaybe A) : @myMaybe B :=
    match mf with
        | empty => empty B
        | just f => match m with
            | empty => empty B
            | just x => just B (f x)
        end
    end.

Definition joinMaybe {A : Type} (mm : @myMaybe (@myMaybe A)) : @myMaybe A :=
    match mm with
        | empty => empty A
        | just m => m
    end.

Instance maybe_functor : Functor myMaybe := {
    fmap := @maybeMap
}.
Proof.
    intros.
    unfold compose.
    unfold maybeMap.
    destruct c.
    reflexivity.
    reflexivity.
    intros.
    unfold maybeMap.
    destruct c.
    unfold id.
    reflexivity.
    unfold id.
    reflexivity.
Defined.

Instance maybe_applicative : Applicative myMaybe := {
    unit := @just;
    apply := @applyMaybe
}.
Proof.
    - intros. unfold applyMaybe. destruct x as [| x']. reflexivity. unfold id. reflexivity.
    - intros.
        unfold applyMaybe.
        destruct u as [| uf].
        reflexivity.
        destruct v as [| vf].
        reflexivity.
        destruct w as [| w'].
        reflexivity.
        unfold compose.
        reflexivity.
    - intros.
        unfold applyMaybe.
        reflexivity.
    -   intros.
        unfold applyMaybe.
        destruct u as [| uf].
        reflexivity.
        reflexivity.
    -   intros.
        simpl.
        destruct x as [| x'].
        unfold maybeMap.
        reflexivity.
        unfold maybeMap.
        reflexivity.
Defined.

Instance maybe_monad : Monad myMaybe := {
    join := @joinMaybe
}.
Proof.
    - intros.
        unfold joinMaybe.
        unfold fmap.
        unfold is_functor.
        unfold maybe_applicative.
        unfold maybe_functor.
        unfold maybeMap.
        unfold unit.
        reflexivity.
    - intros.
        unfold id.
        unfold joinMaybe.
        unfold fmap.
        unfold is_functor.
        unfold maybe_applicative.
        unfold maybe_functor.
        unfold maybeMap.
        destruct m as [| x].
        reflexivity.
        unfold unit.
        reflexivity.
    - intros.
        unfold fmap.
        unfold is_functor.
        unfold maybe_applicative.
        unfold maybe_functor.
        unfold maybeMap.
        destruct m as [| x].
        simpl.
        reflexivity.
        destruct (k x) as [| kx].
        simpl.
        reflexivity.
        simpl.
        reflexivity.
Defined.
