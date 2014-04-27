Definition id {A : Type} (a : A) : A := a.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B): A -> C :=
    fun (a : A) => g (f a).


