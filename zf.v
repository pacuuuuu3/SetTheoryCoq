Section Conjuntos.

  Require Import Classical.
  
  (* Definición del tipo conjunto *)
  Parameter conj: Type.
  
  (* Relación de pertenencia *)
  Parameter elem: conj -> conj -> Prop.
  
  Notation "x ∈ y" := (elem x y) (at level 60).
  
  (* Relación subconjunto *)
  Definition subconj (x y :conj) : Prop :=
    forall z:conj, elem z x -> elem z y.
  
  Notation "x ⊆ y" := (subconj x y) (at level 60).
  
  (* Todo elemento es subconjunto de sí mismo *)
  Lemma subconj_reflex: forall x:conj, subconj x x.
  Proof.
    intros.
    unfold subconj.
    trivial.
  Qed.
  
  (* La relación subconjunto es transitiva *)
  Lemma subconj_trans: forall x y z:conj, subconj x y -> subconj y z -> subconj x z.
  Proof.
    unfold subconj.
    intros.
    apply H in H1.
    apply H0 in H1.
    trivial.
  Qed.
  
  (* Axioma 1: Extensionalidad *)
  Axiom ext_conj: forall x y: conj, (forall z:conj, elem z x <-> elem z y) -> x = y.
  
(* Aquí pruebo que la extensionalidad implica que a ⊆ b y b ⊆ a -> a = b *)
  Lemma ext_subconj: forall x y: conj, subconj x y -> subconj y x -> x = y.
  Proof.
    intros.
    apply ext_conj.
    unfold subconj in *.
    split.
    apply H.
    apply H0.
  Qed.
  
  Parameter vacio : conj.
  
  Notation "∅" := vacio.
  
  (* Axioma 2: Vacío *)
  Axiom vacio_conj: forall y:conj, ~(elem y vacio).
  
  (* Todo conjunto o es vacío o tiene elementos *)
  Theorem dic_conj: forall c:conj, c = vacio \/ exists x, elem x c. 
  Proof.
    intro.
    classical_left.
    unfold not in H.
    
  Qed.
    
  (* Axioma 2: ∈-induction (La relación de pertenencia cumple el principio de inducción *)
    (* Axiom ind_conj: forall P : conj -> Prop, (forall X, (forall x, elem x X -> P x) -> P X) ->  *)
    
  
End Conjuntos.

