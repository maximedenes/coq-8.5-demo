Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Reserved Notation "a ≡ b" (at level 70).

Goal exists n:nat, n=0.
Proof.
  exists 0.

















  Undo.
  eexists.
  reflexivity.
Qed.









Record AbGr := {
  El :> Type ;
  equ : El -> El -> Prop
    where "a ≡ b" := (equ a b);
  equ_equiv : Equivalence equ ;
  zero : El
    where "0" := zero;
  plus : El -> El -> El
    where "x +  y" := (plus x y);
  plus_proper : Proper (equ ==> equ ==> equ) plus ;
  minus : El -> El
    where "- x" := (minus x);
  minus_proper : Proper (equ ==> equ) minus ;

  plus_assoc : forall x y z, (x+y)+z ≡ x+(y+z) ;
  plus_comm : forall x y, x+y ≡ y+x ;
  zero_neutral : forall x, x+0 ≡ x ;
  minus_inverse : forall x, x+(-x) ≡ 0
}.
(* 12 fields including 7 proof obligations. *)

Goal forall (P:AbGr->Prop), exists G, P G.
Proof.
  intros *.
  eexists.













  Undo.
  refine (ex_intro _ _ _).
  - refine {|
      El := Z.t;
      equ n p := Z.eqb n p = true;
      zero := 0%Z;
      plus := Z.add;
      minus := Z.opp
    |}.
Abort.







Goal exists n:nat, n=0.
Proof.
  refine (ex_intro _ _ _).
  1:shelve.
Abort.






Goal exists n:nat, n=0.
Proof.
  refine (ex_intro _ _ _); shelve_unifiable.
Abort.







Goal (exists n:nat, n=0) /\ True.
Proof.
  split; [ refine (ex_intro _ _ _) | ].
  2: reflexivity.
  trivial.
Qed.
















Goal True /\ True.
Proof.
  split.
    all: trivial.
Qed.

















Goal forall (A B C D:Prop), (A->C) -> (B->C) -> (D->C) -> B -> C.
Proof.
  intros * h0 h1 h2 h3.
  Fail (apply h0||apply h1);apply h3.


















  (apply h0 + apply h1);apply h3.




















  Undo.
  Fail once (apply h0 + apply h1);apply h3.





















  Fail ((apply h0+apply h2) || apply h1); apply h3.

  ((apply h0+apply h1) || apply h2); apply h3.
Qed.
























Ltac give_up_quick := trivial || admit.


Goal True /\ exists n, n=0.
Proof.
  split.
  - give_up_quick.
  - give_up_quick.
Qed.
































Goal True.
Proof.
  Fail exactly_once (trivial+trivial).
  exactly_once (trivial+fail).
Qed.
