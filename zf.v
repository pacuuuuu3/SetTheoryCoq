Section Conjuntos.
  
  (* Tercero excluído *)
  Axiom classic: forall P : Prop, P \/ ~P.

  (* Tipo conjunto *)
  Parameter conj : Type.

  (* Operación pertenece *)
  Parameter elem : conj -> conj -> Prop.

  Notation "x ∈ X" := (elem x X) (at level 60).
  Notation "x ∉ X" := (~elem x X) (at level 60).

  (* Definición de contención *)
  Definition subconj (X Y :conj) : Prop :=
    forall x: conj, elem x X -> elem x Y.

  Notation "X ⊆ Y" := (subconj X Y) (at level 60).

  (* La contención es reflexiva *)
  Lemma subconj_reflex: forall A, subconj A A.
  Proof.
    unfold subconj.
    intros.
    exact H.
  Qed.

  (* La contención es transitiva *)
  Lemma subconj_trans: forall A B C, subconj A B -> subconj B C -> subconj A C.
  Proof.
    unfold subconj.
    intros.
    apply H0.
    apply H.
    exact H1.
  Qed.

  (** AXIOMAS **)
  (* Axioma 1: Extensionalidad *)
  Axiom ext_conj: forall X Y, (forall u, elem u X <-> elem u Y) -> X = Y.
  
  Parameter par: conj -> conj -> conj.
  Notation "{ X }" := (par X X).
  Notation "{ X , Y }" := (par X Y) (at level 60).
  
  (* Axioma 2: Axioma del par *)
  Axiom par_conj: forall a b x, elem x (par a b) <-> x = a \/ x = b.

  (* Axioma (o familia de axiomas) 3: Subconjunto o Comprensión *)
  Axiom compr_conj: forall (A: conj->Prop) (a:conj), exists x, forall y, elem y x <-> elem y a /\ A y.  

  Parameter union: conj -> conj.
  Notation "⋃ x" := (union x) (at level 60).
  
  (* Axioma 4: Unión *)
  Axiom union_conj: forall X u, elem u (union X) <-> (exists z, elem z X /\ elem u z). 

  Parameter potencia 
  
  
End Conjuntos.