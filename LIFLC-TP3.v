Require Import Utf8.

(*
   Documentations: 
       * #<a href="https://coq.inria.fr/distrib/current/refman/Reference-Manual018.html">CoqIDE</a>#
       * #<a href="http://lim.univ-reunion.fr/staff/fred/Enseignement/IntroCoq/Exos-Coq/Petit-guide-de-survie-en-Coq.html">Petit guide de survie en Coq</a>#
       * #<a href="http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf">Cheat sheet</a>#
       * #<a href="https://www.lri.fr/~paulin/MathInfo2/coq-survey.pdf">Coq Survey</a> (Guide coq de Christine Paulin-Mohring)</a>#

   Charger le fichier #<a href="LIFLC-TP3.v">LIFLC-TP3.v</a>#, qui est
   à compléter dans ce TP, dans CoqIDE.

 *)


(* Quelques erreurs de raisonnement fréquentes
    
   On peut montrer que ces raisonnements sont faux en Coq.
 *)

(* ex falso sequitur quodlibet *)
Lemma ex_falso : forall P, False -> P.
Proof.
Admitted.

(* erreur très fréquente *)
Definition dyslexic_imp := ∀ P Q:Prop, (P → Q) → (Q → P).
(* Pour cette preuve il faut appliquer une hypothèse contenant des
   quantificateurs forall. Si H est le nom de l'hypothèse, 

   apply (H toto) 

   permet d'appliquer H en remplaçant la variable quantifiée par toto.
   Si plusieurs variables sont quantifiées, on peut écrire 

   apply (H toto titi)
*)
Goal dyslexic_imp -> False.
Proof.
Admitted.

(* erreur très fréquente, bis *)
Definition dyslexic_contrap := ∀ P Q:Prop, (P → Q) → (~P → ~Q).
Goal dyslexic_contrap -> False.
Proof.
Admitted.

(*
   Quelques équivalences remarquables en logique du premier ordre
 *)

(* on ouvre une section pour alléger les assertions *)
Section Basic_FOL.

Variable U : Type.                  (*le type du domaine *)
Variable P Q : U -> Prop.           (*des prédicats unaires *)
Variable R S : U -> U -> Prop.      (*des prédicats binaires, ie des relations *)


Lemma neg_exists_equiv_forall_neg : (~ ∃ x , P x ) <-> ∀ x , ~ P x .
Proof.
Admitted.


Lemma exists_is_or : (∃ x , P x ∨ Q x) <-> (∃ x,  P x) ∨ (∃ x, Q x).
Proof.
Admitted.

Lemma forall_is_and : (∀ x , P x /\ Q x) <-> (∀ x,  P x) /\ (∀ x, Q x).
Proof.
Admitted.



Lemma forall_implies_neg_exists_neg  : (∀ x, P x)→ ~(∃ y, ~ P y).
Proof.
Admitted.



Goal (∃ x, (∀ F:U → Prop, F x)) → 2 = 3.
Proof.
Admitted.



Goal (∀ x y, (P(x) ∧ (P(y) -> Q(x)))) -> ∀x, Q(x).
Proof.
Admitted.

(* si qq'un est aimé de tous, alors tout le monde aime qq'un *)
Goal (∃ y, ∀ x, R x y) -> (∀ x, ∃ y, R x y).
Proof.
Admitted.


Goal (∃ y, ∀ x, R x y) -> (∃ x, R x x).
Proof.
Admitted.

End Basic_FOL.


Section Ensembles.
(* On va maintenant prouver quelques propriétés des ensembles dont les
   élements sont d'un certain type U.
 *)
Variable U : Type.
  
(* Un ensemble E peut être représenté par un prédicat unaire qui est
   vrai lorsque son argument est un élément de E. On utilise cela pour
   cela Prop (le type des proposition de Coq). Les ensembles sont donc
   vus comme de type U -> Prop. Une manière de le comprendre est voir
   un ensemble comme une fonction qui prend un élement et donne une
   formule qui sera vraie si cet élement est dans l'ensemble. *)
Definition Ensemble := U -> Prop.

(* On peut alors redéfinir l'appartenance (In) de x à E comme le fait
   que le prédicat qui représente E est vrai.  *)
Definition In (A:Ensemble) (x:U) : Prop := A x.
Notation "x ∈ E" := (In E x)  (at level 45, right associativity).

(* Les définitions suivantes se construisent naturellement à partir de
   celle de appartient (In). *)
Definition Included (A B:Ensemble) : Prop := forall x, x ∈ A -> x ∈ B.
Notation "A ⊆ B" := (Included A B)  (at level 70, right associativity).

Definition Cup (A B:Ensemble) : U -> Prop := fun x => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (Cup A B)  (at level 70, right associativity).

Definition Cap (A B:Ensemble) : U -> Prop := fun x => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (Cap A B)  (at level 70, right associativity).

Definition Empty : U -> Prop := fun x => False .
Notation "∅" := (Empty).

Definition Setminus (B C:Ensemble) : Ensemble := fun x:U => x ∈ B /\ ~ x ∈ C.
Notation "A \ B" := (Setminus A B)  (at level 80, right associativity).

(* Cet axiome permet de déduire une égalité à partir de la double
   inclusion. *)
Axiom Extensionality_Ensembles : forall A B:Ensemble,  (A ⊆ B /\ B ⊆ A) -> A = B.

Variable A B C: Ensemble.

(* Exemple pour comprendre comment utiliser les définitons ci-dessus *)
(* Réflexivité de ⊆ *)
Goal A ⊆ A.
Proof.
  unfold Included.
  intros x.
  auto.
Qed.

(* Transitivité de ⊆.

   Remarque: Avec la réflexivité et l'axiome Extensionality_Ensembles,
   on a que ⊆ est un ensemble.

 *)
Goal A ⊆ B -> B ⊆ C  -> A ⊆ C.
Proof.
Admitted.

Goal ∅ ⊆ A.
Proof.
Admitted.

Goal A ⊆ B <-> (A ∩ B) = A.
Proof.
Admitted.

(* exo de td lif LF *)
Goal  (A \ (B ∪ C)) = ((A \ B) ∩ (A \ C)).
Proof.
Admitted.


Goal A ⊆ B -> (A \ B) = ∅.
(* la réciproque est DIFFICILE *)
Proof.
Admitted.
 
End Ensembles.
