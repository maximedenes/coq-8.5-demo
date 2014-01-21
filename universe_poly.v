Require Import Utf8.

Definition idmono {A : Type} (a : A) := a.

Fail Definition selfapp : forall A, A -> A := 
  idmono (@idmono).




























Polymorphic Definition id {A : Type} (a : A) := a.

Definition selfapp : forall A, A -> A := id (@id).

Set Printing All.
Set Printing Universes.
Print selfapp.



























(** Polymorphic inductives *)

Polymorphic Inductive pprod (A B : Type) :=
  | ppair (a : A) (b : B).

Arguments ppair {A B} a b.

Definition U2 := Type.
Definition U1 := Type : U2.
Definition U0 := Type : U1.

Inspect 3.

(* U2 -> Type 19 *)
(* U1 -> Type 20 *)
(* U0 -> Type 21 *)

(** Polymorphic definitions *)

Polymorphic Definition twice (u : Type) := 
  pprod u u -> pprod u u.

Let twiceU0 := twice U0.
Let twiceU1 := twice U1.

Print twiceU0.
Print twiceU1.

Check (twiceU1 : U2).
Check (twiceU0 : U1).

Fail Check (twiceU0 : U0).

(* With cumulativity *)
Check (twiceU0 : U2).





















(** Types in records *)

Module MonomorphicMagma.

  Record magma := 
    { magma_carrier :> Type;
      magma_op : magma_carrier → magma_carrier → magma_carrier }.
  
  Definition magma_nat : magma := 
    {| magma_carrier := nat;
       magma_op x y := plus x y |}.
  
  Definition magma_product (x : magma) (y : magma) :=
    {| magma_carrier := (x * y);
       magma_op t u := 
         let '(t1, t2) := t in
         let '(u1, u2) := u in
           (magma_op x t1 u1, magma_op y t2 u2)
    |}.
  
  Fail Definition magma_magma : magma :=
    {| magma_carrier := magma;
       magma_op := magma_product |}.

End MonomorphicMagma.



















(* With polymorphism *)

Module PolymorphicMagma.
  Set Universe Polymorphism.

  Record magma := 
    { magma_carrier :> Type;
      magma_op : magma_carrier → magma_carrier → magma_carrier }.
  
  Definition magma_nat : magma := 
    {| magma_carrier := nat;
       magma_op x y := plus x y |}.
  
  Definition magma_product (x : magma) (y : magma) :=
    {| magma_carrier := pprod x y;
       magma_op t u := 
         let 'ppair t1 t2 := t in
         let 'ppair u1 u2 := u in
           ppair (magma_op x t1 u1) (magma_op y t2 u2)
    |}.
  
  Monomorphic Definition magma_magma : magma :=
    {| magma_carrier := magma;
       magma_op := magma_product |}.

End PolymorphicMagma.

(** Magma is instantiated at 2 incompatible levels in
  [magma_magma] *)

Print PolymorphicMagma.magma_magma.
Test Universe Polymorphism.





























(** Internalized translations: *)

Polymorphic Inductive sigma (A : Type) (P : A -> Type) :=
  dpair : ∀ a : A, P a -> sigma A P.

Notation " { x : A & P } " := (@sigma A (fun x : A => P)) : type_scope.
Notation " { x & P } " := (@sigma _ (fun x => P)) (at level 0, x at level 99) : type_scope.

Polymorphic Inductive paths {A : Type} : A -> A -> Type :=
  idpath : forall a, @paths A a a.

Polymorphic Definition contr (A : Type) := 
  forall x : A, { y : A & paths x y }.

Polymorphic Definition _Type := 
  { A & contr A }.

Print _Type.


(** Sigma is now polymorphic, only one exists... *)

Definition subset {A : Set} (P : A → Prop) : Set := 
  sigma A P.

Definition subsetT {A : Type} (P : A → Prop) := 
  sigma A P.

Definition conj (A B : Prop) : Prop :=
  sigma A (fun _ => B).

