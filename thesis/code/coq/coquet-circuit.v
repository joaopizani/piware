Context {tech : Techno}
Inductive Circuit : Type -> Type -> Type :=
| Atom : forall {n m : Type} {Hfn : Fin n} {Hfm : Fin m},
             techno n m -> Circuit n m

| Plug : forall {n m : Type} {Hfn : Fin n} {Hfm : Fin m} (f : m -> n),
             Circuit n m

| Ser  : forall {n m p : Type},
             Circuit n m -> Circuit m p -> Circuit n p

| Par  : forall {n m p q : Type},
             Circuit n p -> Circuit m q -> Circuit (n + m) (p + q)

| Loop : forall {n m p : Type},
             Circuit (n + p) (n + p) -> Circuit n m
