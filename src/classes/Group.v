Class Magma (A : Type) := {
    (** A Magma is just a Set/Type with a binary operation *)

    mplus : A -> A -> A
}.

Notation "a <+> b" := (mplus a b) (at level 70).

Class Semigroup (A : Type) := {

    (** A semigroup is a Magma *)
    is_magma :> Magma A;

    (** Associativity law: The binary operation must be associative *)
    semigroup_associativity
        : forall (x y z : A)
        , (x <+> (y <+> z)) = ((x <+> y) <+> z)

}.

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

Class Group(A: Type) := {

    (** A Group is a Monoid *)
    is_monoid :> Monoid A;

    invert : A -> A;

    group_inverse_left
        : forall (a : A)
        , (invert a) <+> a = midentity;

    group_inverse_right
        : forall (a : A)
        , a <+> (invert a) = midentity
}.

Fixpoint exp {A : Type} {isgroup : Group A} (a : A) (n : nat) : A :=
    match n with
        | O => midentity
        | S m => a <+> exp a m
    end.

Inductive magma_homomorphism (A B : Type) (f : A -> B) {a_magma : Magma A} {b_magma : Magma B} : Type :=
    | magma_hom : forall (a b : A), (f (a <+> b) = ((f a) <+> (f b))) -> magma_homomorphism A B f.

Inductive monoid_homomorphism (A B : Type) (f : A -> B) {a_monoid : Monoid A} {b_monoid : Monoid B} : Type :=
    | monoid_hom : magma_homomorphism A B f -> (f midentity = midentity) -> monoid_homomorphism A B f.

Inductive group_homomorphism (A B : Type) (f : A -> B) {a_group : Group A} {b_group : Group B} : Type :=
    | group_hom : forall (a : A), monoid_homomorphism A B f -> (f (invert a) = invert (f a)) -> group_homomorphism A B f.

Inductive inclusion : Type :=
    | included : inclusion
    | excluded : inclusion.

Inductive subset (A : Type) : Type :=
    | inclusion_function : (A -> inclusion) -> subset A.

Definition isInSubset {A : Type} (a : A) (s : subset A) : inclusion :=
    match s with
      | inclusion_function f => f a
    end.

Inductive elementOf {A : Type} (a : A) (s : subset A) : Prop :=
    | elementIncluded : (isInSubset a s = included) -> elementOf a s.

Inductive nonempty {A : Type} (s : subset A) : Prop :=
    | exists_element : (exists (x : A), elementOf x s) -> nonempty s.

Inductive is_subgroup (A : Type) (g : subset A) {a_group : Group A} : Prop :=
    | closed_subset : forall (a b : A), (elementOf a g -> elementOf b g -> elementOf (a <+> b) g) -> (elementOf a g -> elementOf (invert a) g) -> elementOf midentity g -> is_subgroup A g.

Theorem x_yinverse_subgroup_test
    : forall (A : Type) (s : subset A) (x y : A) (isgroup : Group A)
    , nonempty s -> elementOf x s -> elementOf y s -> elementOf (x <+> (invert y)) s -> is_subgroup A s.
Proof.
    intros.
    destruct H.
    destruct H0.
    destruct H1.
    destruct H2.

Inductive generator_group (A : Type) (r : A) : Type :=
    | ZeroPower : generator_group A r
    | NonZeroPower : generator_group A r -> generator_group A r.

Fixpoint expGeneratorGroup {A : Type} {r : A} {isgroup : Group A} (g : generator_group A r) : A :=
    match g with
        | ZeroPower => midentity
        | NonZeroPower n => r <+> (expGeneratorGroup n)
    end.

Fixpoint generatorPlus {A : Type} {r : A} (x : generator_group A r) (y : generator_group A r) : (generator_group A r) :=
    match x with
        | ZeroPower           => y
        | NonZeroPower n => NonZeroPower A r (generatorPlus n y)
    end.

Instance generator_magma : forall (A : Type) (r : A), Magma (generator_group A r) := {
    mplus := @generatorPlus A r
}.

Instance generator_semigroup : forall (A : Type) (r : A), Semigroup (generator_group A r) := {
}.
Proof.
    intros.
    simpl.
    induction x as [| x'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHx'.
      reflexivity.
Defined.

Instance generator_monoid : forall (A : Type) (r : A), Monoid (generator_group A r) := {
    midentity := ZeroPower A r
}.
Proof.
    - intros.
      simpl.
      reflexivity.
    - intros.
      simpl.
      induction a as [| a'].
      simpl.
      reflexivity.
      simpl.
      rewrite IHa'.
      reflexivity.
Defined.

(** Oops, the generator "group" at this stage only includes the nats, which is wrong, it should allow for negative integers as well, as such it is not actually a group atm....*)

(**Theorem generator_subgroup
    : forall (A : Type) (r : A) (a_group : Group A)
    , subgroup (generator_group A r) A (@expGeneratorGroup A r a_group).
*)