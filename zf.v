Section Conjuntos.
  
  Require Import Setoid.
  
  (* Tipo conjunto *)
  Parameter conj : Type.

  (* Decidibilidad de igualdad... *)
  Parameter eq_dec : forall x y : conj, { x=y } + { ~ x=y }.
  
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

  (* Regreso de la extensionalidad. *)
  Theorem ext_regreso: forall X Y, X = Y -> (forall u, elem u X <-> elem u Y).
  Proof.
    intros.
    rewrite H.
    split;trivial.
  Qed.

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

  (* Operación potencia *)
  Parameter potencia: conj -> conj.

  (* Axioma 5: Potencia *)
  Axiom pot_conj: forall X u, elem u (potencia X) <-> subconj u X. 

  (* Existe al menos un conjunto *)
  Axiom conjunto : conj.
  
  (* Existe un conjunto vacío *)
  Theorem vacio_conj: exists x, forall y, ~elem y x.
  Proof.
    unfold not.
    assert (exists x, forall y, elem y x <-> elem y conjunto /\ ~elem y conjunto).
    apply compr_conj.
    destruct H.
    exists x.
    intros.
    apply H in H0.
    unfold not in H0.
    destruct H0.
    apply H1 in H0.
    trivial.
  Qed.
  
  Parameter vacio:conj.
  Notation "∅" := vacio.
  Axiom vacio_def: forall y, ~elem y vacio.
  
  (* Axioma 6: Infinito *)
  Axiom inf_conj: exists S, elem vacio S /\ (forall x, elem x S -> elem (unionc x (par x x)) S).
  
  (* Axioma 7: Reemplazo. La imagen de un conjunto es un conjunto 
   * Codifiqué la función como una propiedad por facilidad *)
  Axiom rempl_conj: forall (A : conj->conj->Prop) (a:conj), exists x,forall y, elem y a -> ((exists z, A y z) -> (exists z, elem z x /\ A y z)).

  Parameter inter: conj -> conj -> conj.    
  Axiom intersec: forall x y z, elem z (inter x y) <-> elem z x /\ elem z y.

  (* Introducción de la unión *)
  Lemma union_intro: forall x y z, elem z x -> elem z (unionc x y).
  Proof.
    intros.
    unfold unionc.
    apply union_conj.
    exists x.
    split.
    apply par_conj.
    left;trivial.
    trivial.
  Qed.
  
  (* Existe la intersección y es única. *)
  Theorem inter_exists: forall x y, exists z, (forall w, elem w z <-> elem w x /\ elem w y) /\ z = (inter x y).
  Proof.
    intros.
    assert (exists z, forall w, elem w z <-> elem w (unionc x y) /\ (elem w x /\ elem w y)).
    apply compr_conj.
    destruct H.
    exists x0.
    split.
    intros.
    split.
    intro.
    apply H in H0.
    intuition.
    intro.
    assert (elem w (unionc x y)).
    apply union_intro.
    intuition.
    apply H.
    intuition.
    apply ext_conj.
    intro.
    split.
    intro.
    apply H in H0.
    apply intersec.
    intuition.
    intro.
    apply intersec in H0.
    assert (elem u (unionc x y)).
    apply union_intro.
    intuition.
    apply H.
    intuition.
  Qed.
        
  (* Axioma 8: Fundación *)
  Axiom fund_conj: forall S, ~ S = vacio -> (exists x, elem x S /\ (inter S x = vacio)).

  (* Ningún conjunto se pertenece *)
  Theorem c_not_int_c: forall c, ~ elem c c.
  Proof.
    intro.
    unfold not.
    intro.
    assert (exists x, x = par c c).
    exists (par c c).
    trivial.
    destruct H0.
    assert (exists y, elem y x /\ (inter x y = vacio)).
    apply fund_conj.
    intro contra.
    rewrite H0 in contra.
    assert (elem c vacio).
    assert (elem c (par c c)).
    apply par_conj.
    left;trivial.
    rewrite contra in H1.
    trivial.
    apply vacio_def in H1.
    trivial.
    rewrite H0 in H1.
    destruct H1.
    destruct H1.
    apply par_conj in H1.
    assert (elem c (inter (par c c) x0)).
    apply intersec.
    split.
    apply par_conj.
    left;trivial.
    destruct H1;rewrite H1;trivial.
    rewrite H2 in H3.
    contradict H3.
    apply vacio_def.
  Qed.
  
  (* El axioma de elección ya está en coq así que no lo voy a poner *)

  (* Definición de naturales *)
  Definition cero := vacio.
  Definition suc (x:conj) : conj :=
    unionc x (par x x).

  (* El conjunto de los naturales es conjunto *)
  Theorem existen_nat: exists n, (elem cero n /\ (forall z, elem z n -> elem (suc z) n)).
  Proof.
    apply inf_conj.
  Qed.

  (* Simplemente le doy nombre a los naturales *)
  Parameter naturales:conj.
  Axiom naturales_def: elem cero naturales /\ (forall z,elem z naturales -> elem (suc z) naturales).

  (* Definición de par ordenado *)
  Definition par_ordenado (a b : conj) : conj :=
    par (par a a) (par a b).


  (* Igualdad en pares implica igualdad *)
  Lemma igualdad_pares: forall x y, par x x = par y y -> x = y.
  Proof.
    intros.
    assert (elem x (par y y)).
    rewrite <- H.
    apply par_conj.
    left;trivial.
    apply par_conj in H0.
    case H0;trivial.
  Qed.
  
  (* Probar que dos pares ordenados son iguales sii tienen los mismos 
   * conjuntos en el mismo orden. *)
  Theorem pares_ord_bien: forall a b c d, par_ordenado a b = par_ordenado c d <-> a = c /\ b = d. 
  Proof.
    (* Caso 1: a = b *)
    intros.
    unfold par_ordenado.
    destruct (eq_dec a b).
    rewrite e.
    split.
    intro.
    assert (elem (par c c) (par (par b b) (par b b))).
    rewrite H.
    apply par_conj.
    left;trivial.
    assert (c = b).
    apply par_conj in H0.
    destruct H0; apply igualdad_pares in H0; trivial.
    split.
    intuition.
    rewrite H1 in H.
    assert (elem (par b d) (par (par b b) (par b b))).
    rewrite H.
    apply par_conj.
    right;trivial.
    apply par_conj in H2.
    destruct H2.
    assert (elem d (par b b)).
    rewrite <- H2;apply par_conj; right; trivial.
    apply par_conj in H3.
    destruct H3; intuition.
    assert (elem d (par b b)).
    rewrite <- H2;apply par_conj; right; trivial.
    apply par_conj in H3.
    destruct H3; intuition.
    intros.
    destruct H.
    rewrite <- H.
    rewrite <- H0.
    trivial.
    (* Caso 2: a != b *)
    split.
    intro.
    destruct (eq_dec c d).
    rewrite e in H.
    assert (elem (par a b) (par (par d d) (par d d))).
    rewrite <- H.
    apply par_conj; right;trivial.
    apply par_conj in H0.
    destruct H0.
    assert (elem b (par d d)).
    rewrite <- H0; apply par_conj; right;trivial.
    apply par_conj in H1.
    assert (elem a (par d d)).
    rewrite <- H0; apply par_conj; left;trivial.
    apply par_conj in H2.
    destruct H1,H2.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    assert (elem b (par d d)).
    rewrite <- H0; apply par_conj; right;trivial.
    apply par_conj in H1.
    assert (elem a (par d d)).
    rewrite <- H0; apply par_conj; left;trivial.
    apply par_conj in H2.
    destruct H1,H2.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    rewrite H2 in n.
    rewrite H1 in n.
    contradiction.
    assert ((par a a) <> (par c d)).
    intro.
    assert(elem d (par a a)).
    rewrite H0; apply par_conj; right; trivial.
    assert(elem c (par a a)).
    rewrite H0; apply par_conj; left; trivial.
    apply par_conj in H1.
    apply par_conj in H2.
    destruct H1, H2; rewrite H1 in n0; rewrite H2 in n0; contradiction.
    assert (elem (par a a) (par (par c c) (par c d))).
    rewrite <- H.
    apply par_conj; left; trivial.
    apply par_conj in H1.
    destruct H1.
    split.
    apply igualdad_pares.
    trivial.
    assert (elem (par a b) (par (par c c) (par c d))).
    rewrite <- H; apply par_conj; right; trivial.
    apply par_conj in H2.
    destruct H2.
    rewrite <- H1 in H2.
    assert (b = a).
    assert (elem b (par a a)).
    rewrite <- H2; apply par_conj; right; trivial.
    apply par_conj in H3; destruct H3; trivial.
    symmetry in H3.
    contradiction.
    assert (a = c).
    apply igualdad_pares.
    trivial.
    rewrite H3 in H2.
    assert (elem b (par c d)).
    rewrite <- H2; apply par_conj; right; trivial.
    apply par_conj in H4.
    destruct H4.
    rewrite <- H4 in H3; contradiction.
    trivial.
    contradiction.
    intro.
    destruct H.
    rewrite H.
    rewrite H0.
    trivial.
  Qed.
    
End Conjuntos.