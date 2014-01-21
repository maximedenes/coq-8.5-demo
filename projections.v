Module Legacy.

  Record foo (A : Type) := 
    { bar : A -> A }.

  Definition test A (f : foo A) : 
    bar _ f = id (bar _ f).
  Proof.   
    Set Printing All.

    unfold bar.

    reflexivity.
  Qed.
  

End Legacy.
  
Module Primitive.

  Set Primitive Projections.

  Record foo (A : Type) := 
    { bar : A -> A }.


  Definition test A (f : foo A) : 
    bar f = id f.(bar).
  Proof.   
    Set Printing All. idtac.

    unfold bar.

    reflexivity.
  Qed.

  Eval compute in @bar.

  Lemma eta A (f : foo A) : 
    f = {| bar := f.(bar) |}.
  Proof. reflexivity. Defined. 

End Primitive.



  

