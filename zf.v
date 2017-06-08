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
  Notation "{ X , Y }" := (par X Y) (at level 60).

  (* Unitario de X *)
  Notation "{ X }" := (par X X).
  
  (* Axioma 2: Axioma del par *)
  Axiom par_conj: forall a b x, elem x (par a b) <-> x = a \/ x = b.

  (* Axioma (o familia de axiomas) 3: Subconjunto o Comprensión *)
  Axiom compr_conj: forall (A: conj->Prop) (a:conj), exists x, forall y, elem y x <-> elem y a /\ A y.  

  Parameter union: conj -> conj.
  Notation "⋃ x" := (union x) (at level 60).

  (* Unión de dos conjuntos *)
  Definition unionc (a b: conj) : conj :=
    union (par a b).
  
  Notation "a ∪ b" := (unionc a b) (at level 60). 
  
  (* Axioma 4: Unión *)
  Axiom union_conj: forall X u, elem u (union X) <-> (exists z, elem z X /\ elem u z). 

  Parameter potencia: conj -> conj.

  (* Axioma 5: Potencia *)
  Axiom pot_conj: forall X u, elem u (potencia X) <-> subconj u X. 

  (* Existe un conjunto. Para facilitarme las cosas, diré que es el vacío. *)
  Parameter vacio:conj.
  Notation "∅" := vacio. 

  (* Axioma 6: Infinito *)
  Axiom inf_conj: exists S, elem vacio S /\ (forall x, elem x S -> elem (unionc x (par x x)) S).
  
  (* Axioma 7: Reemplazo. La imagen de un conjunto es un conjunto 
   * Codifiqué la función como una propiedad por facilidad *)
  Axiom rempl_conj: forall (A : conj->conj->Prop) (a:conj), exists x,forall y, elem y a -> ((exists z, A y z) -> (exists z, elem z x /\ A y z)).

  Definition intersec: 
  
  (* Axioma 8: Fundación *)
  
  
End Conjuntos.