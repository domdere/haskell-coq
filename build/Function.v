Definition id {A : Type} (a : A) : A := a.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B): A -> C :=
    fun (a : A) => g (f a).

Axiom extensional_equality : forall (A B : Type)
 (f : A -> B)
 (f': A -> B),
 (forall x, f x = f' x) ->
  f = f'.

Theorem compose_left_identity
    : forall (A B : Type) (f : A -> B)
    , compose id f = f.
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold compose.
    unfold id.
    reflexivity.
Qed.

Theorem compose_right_identity
    : forall (A B : Type) (f : A -> B)
    , compose f id = f.
Proof.
    intros.
    apply extensional_equality.
    intros.
    unfold compose.
    unfold id.
    reflexivity.
Qed.
