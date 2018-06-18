(* 
   L'objectif de ce TP est de  poursuivre la prise en main l'outil Coq
   à   travers  quelques   exercices  sur   les  types   inductifs  et
   l'induction.   On verra  également comment  utiliser des  théorèmes
   existants.

 
   Documentations: 
       * #<a href="https://coq.inria.fr/distrib/current/refman/Reference-Manual018.html">CoqIDE</a>#
       * #<a href="http://lim.univ-reunion.fr/staff/fred/Enseignement/IntroCoq/Exos-Coq/Petit-guide-de-survie-en-Coq.html">Petit guide de survie en Coq</a>#
       * #<a href="http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf">Cheat sheet</a>#
       * #<a href="https://www.lri.fr/~paulin/MathInfo2/coq-survey.pdf">Coq Survey</a> (Guide coq de Christine Paulin-Mohring)</a>#



   Charger le fichier #<a href="LIFLC-TP2.v">LIFLC-TP2.v</a>#, qui est
   à compléter dans ce TP, dans CoqIDE.
*)

Require Import Utf8.

Section my_list.

(**********************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                    *)
(**********************************************************************)

(* Ensembles inductifs en Coq.
   
   En  Coq,  il  est  possible d'introduire  ses  propres  dédinitions
   d'ensembles  inductifs.  Cela  se  fait via  des constructeurs,  un
   constructeur correspondant  à une  règle de construction.   Dans le
   cadre de  ce cours,  les constructeurs  ont un  nom et  prennent un
   certains nombre  d'arguments.  Le nom du  constructeur permet aussi
   d'identifier la manière dont on a construit l'élément considéré.
   
   Prenons l'exemple  suivant qui  définie les listes  d'entiers (dans
   Coq, nat est un type pour représenter les entiers naturels):

 *)

Inductive list :=
| nil : list                  (* nil est la liste vide *)
| cons : nat -> list -> list. (* cons a l est la liste obtenue 
                                 en ajoutant a en tête de l *)

(* 
   En  regardant de  plus près  la définition,  on peut  voir que  les
   constructeurs  de liste  sont vu  par Coq  comme des  fonctions qui
   renvoient le type list.

   Le  constructeur nil  ne  prend  pas d'argument,  on  peut donc  le
   considérer comme une constante. Cela correspond au cas de base.

   Au contraire le  constructeur cons prend deux  arguments, un entier
   (type nat) et une liste (type  list). On peut remarquer la forme de
   la définition  du type  de cons  avec des flèches  (nat ->  list -> list) 
   alors qu'on  s'attendrait à  une paire d'arguments  (nat *  list ->  list).  
   
   Ce  type  de  formalisation   est  plus  naturel  en  programmation
   fonctionnelle et n'est sur le fond pas très différent de la version
   classique      à     deux      arguments      (voir     le      #<a
   href="http://liris.cnrs.fr/romuald.thion/files/Enseignement/LIFAP5/LIFAP5-2017P-TD2.pdf">TD2</a>#,
   exercice 6 de LIFAP5 sur la curryfication).
   
   Les  constructeurs  s'utilisent  ensuite  comme  des  fonctions  de
   construction de liste. La syntaxe  du langage est ici également une
   syntaxe fonctionnelle dans laquelle au lieu de passer des arguments
   entre parenthèses et séparés par des  virgules, on les sépare de la
   fonction  par de  simples espaces,  comme dans  un shell  Unix. Les
   parenthèses sont alors utilisées lever les ambiguités et identifier
   les sous-expressions (comme pour  les opérations arithmétiques, les
   formules ou le lambda-calcul vu en LIFAP5).

   Voici quelques listes d'entiers  définies grâce au constructeurs de
   liste:

       * la liste vide: nil
       * la liste à un élément qui contient 3 (fabriquée à partir de 3
         et de la liste vide): cons 3 nil
       * la liste à 2 éléments qui contient 5 et 3 (fabriquée à partir
         5 et de la liste précédente): cons 5 (cons 3 nil)

   On peut demander à Coq de vérifier le type de ces expressions:

 *)

Check nil : list.
Check 3 : nat.
Check cons 3 nil : list.
Check cons 5 (cons 3 nil) : list.

(* 
   Ce principe  d'induction n'est  pas limité aux  liste et  permet de
   construire de nombreux types.

   Par exemple, les  entiers sont définis comme suit en  Coq, avec "S"
   la fonction  successeur, c'est-à-dire +1, c'est  une représentation
   unaire     des     entiers     (qui    est     inefficace)     voir
   https://coq.inria.fr/library/Coq.Init.Datatypes.html

   Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.  
*)


(* On note "a::b::[]" au lieu de "cons a (cons b nil)" pour faciliter
   la rédaction et la lecture: *)
Infix "::" := cons.
Notation "[]" := nil.

(* Les vérifications de type ci-dessus peuvent alors s'écrire: *)
Check [] : list.
Check 3 :: [] : list.
Check 5 :: 3 :: [] : list.


(* Comme nil et cons des  "constructeurs", et comme Coq ne fait AUCUNE
   hypothèse   supplémentaires  sur   l'égalité   entre  termes,   les
   propriétés suivantes sont vérifiées :

    - les images des constructeurs n'ont pas d'éléments en commun; 
    - les constructeurs sont injectifs (sur chacun de leurs arguments).

   En effet,  si ce  n'était pas  le cas,  alors 2  listes construites
   différements pourraient pourraient être égales, par exemple :
    
    - (cons 0 nil) <> nil car (cons 0 nil) et nil doivent donner 
      des résultats différents
    - (cons 0 nil) <> (cons 1 nil) car cons est injectif

   Les  deux  tactiques  associées   qui  permettent  d'exploiter  ces
   propriétés sont respectivement :
    
    - discriminate
    - injection 
*)

(**********************************************************************)
(* Exercice 1 : terminer les preuves et cons_injective                *)
(**********************************************************************)

(* Le mot clé forall permet  d'énoncer des propriétés qui doivent être
   vraies pour  toutes les  valeurs d'une  certaine variable.  On fait
   suivre  forall  du nom  des  variables  concernées. On  sépare  les
   variables d'un espace s'il y en  a plusieurs et on ajoute, avant de
   donner la formule (penser pour le moment "l'énoncé") à vérifier.

   Par exemple:

      - forall x, x+1 <> 0 signifie 
        "pour tous les x, x+1 n'est pas égal à 0"
      - forall x y, x + 1 + y = 1 + x + y signifie 
        "pour tous les x et tous les y, x + 1 + y = 1 + x + y"
 
   En Coq,  la tactique intro permet  de prendre un x  quelconque pour
   faire une preuve générique qui fonctionnera pour tous les x.

   On peut  si on  le souhaite  spécifier le  type des  variables, par
   exemple: forall (x:nat) (xs:list) indique que x est un entier et xs
   une liste.  Sinon Coq tentera de deviner le type.
*)


(* Hint : utiliser discriminate et injection *)

Lemma nil_neq_cons : forall x (l:list), [] <> x :: l.
Proof.
  intros.
  discriminate.
Qed.

Lemma cons_injective : forall x xs y ys, (x::xs) = (y::ys) -> (x = y /\ xs = ys).
Proof.
  intros.
  injection H.
  intros.
  split.
  * assumption.
  * assumption.
Qed.

(**********************************************************************)
(* FONCTION SUR ENSEMBLES INDUCTIFS                                   *)
(**********************************************************************)

(*
  Le mot  clé Definition  permet d'introduire  une nouvelle  valeur en
  Coq.  Comme en LIFAP5, les fonctions sont des valeurs particulières,
  on   utilise   donc   Definition  pour   introduire   de   nouvelles
  fonctions. Les paramètres  de la fonction sont listés  après son nom
  (éventuellement avec leur type) et la velur est indiquée après :=

  Voici 2 définitions de la fonction qui ajoute deux éléments en tête de liste:
 *)

Definition ajoute2 x y l := x :: y :: l.
Definition ajoute2' (x:nat) (y:nat) (l:list) := x :: y :: l.

(* On peut voir le type d'une fonction avec l'instruction About *)
About ajoute2.
About ajoute2'.

(*********************************************************************)

(*  On souhaite  montrer  que  ces deux  fonctions  calculent la  même
   chose.  Pour  cela, on  va  utiliser  leur  définition grâce  à  la
   tactique unfold nom_de_la_fonction. On  pourra utiliser la tactique
   reflexivity pour  conclure lorsqu'on  obtient une  égalité triviale
   (même chose à droite et à gauche):

   Dérouler pas à pas la preuve pour voir l'effet des tactiques.
 *)
Goal forall x y l, ajoute2 x y l = ajoute2' x y l.
Proof.
  intros.
  unfold ajoute2.
  unfold ajoute2'.
  reflexivity.
Qed.
     
(*  Pour  travailler avec  les  ensembles  inductifs, il  est  souvent
   commode  de  pouvoir  définir  des fonctions  travaillant  sur  les
   éléments de cet ensemble. De  telle fonctions sont très souvent des
   fonctions  récursives  définies  par   cas  selon  le  constructeur
   utilisé. Coq met à disposition l'instruction match:

   match valeur with 
   | cas1 => resultat1
   | cas2 => resultat2
   ...
   end

   qui  permet  de  faire  une  telle décomposition  par  cas.  Si  un
   constructeur  prend des  paramètres, on  les ajoute  à la  suite du
   constructeur, ce qui permet de les utiliser dans le résultat.
 *)

Definition est_vide l :=
  match l with
  | nil => True
  | cons x l' => False
  end.
About est_vide.
Check est_vide [] = True.
Check est_vide (3::[]) = False.
Check est_vide (5::3::[]) = False.

(* On peut utiliser les racourcis d'écriture sur les listes dans le match: *)

Definition est_vide' l :=
  match l with
  | [] => True
  | x :: l' => False
  end.
About est_vide'.

(* Si  on souhaite  montrer que  ces deux  fonctions donnent  le même
   résultat, il  faut procéder  par cas  sur la  liste afin  de savoir
   quelle  branche  du match  sera  utilisée.   On peut  utiliser  les
   tactiques induction ou destruct sur une liste et permet de faire un
   raisonnement par cas.

   Dérouler la preuve  suivante pas à pas afin de  voir l'effet de ces
   tactiques.

 *)
Goal forall l, est_vide l = est_vide' l.
Proof.
  intros.
  induction l. (* introduit 2 cas: nil et cons n l *)
  * simpl.
    reflexivity.
  * simpl.
    reflexivity.
Qed.

Goal forall l, est_vide l = est_vide' l.
Proof.
  intros.
  destruct l. (* introduit 2 cas: nil et cons n l *)
  * simpl.
    reflexivity.
  * simpl.
    reflexivity.
Qed.


(**********************************************************************)
(* FONCTIONS RECURSIVES                                               *)
(**********************************************************************)

(*   De  nombreuses fonctions  utiles  travaillant  sur les  ensembles
   inductifs  sont récursives.  Lorsqu'on  veut  définir une  fonction
   récursive, il faut le faire explicitement en Coq avec l'instruction
   Fixpoint à la place de Definition.

   On définit ainsi la concatenation de listes:
*)
Fixpoint append (l1 l2 : list) : list := 
  match l1 with
  | []     => l2
  | x :: l => x::(append l l2)
  end.

(* On note ++ en notation infix pour la concatenation *)
Infix "++" := append.

(* On montre le lemme suivant par simple calcul de la fonction append avec la tactique simpl *)
Lemma append_nil_l : forall l, [] ++  l = l.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Par contre, pour le théorème suivant, un simple calcul sur
   le premier argument ne suffit pas, il faut utiliser le principe
   d'induction de coq sur les listes *)

(* la tactique "rewrite [<-] eq [in H]" où eq est une equation de la forme "x = y"
   et H une hypothèse permet de réécrire un terme x en un terme y (ou y en x avec <-) *)

(* Dérouler les preuves suivantes pas à pas pour en comprendre le fonctionnement. *)

Lemma append_nil_r : forall l, l ++ [] = l.
Proof.
  induction l as [ |n l IHl]. (* on nomme les variables et l'hypothese d'induction *)
  (* l'induction introduit deux cas:
     - la liste vide nil: (pas de variable et pas d'hypothèse d'induction)
     - cons n l: n et l sont des variables et l'hypothèse d'induction nommée IHl *)
  - simpl.
    trivial. 
  - simpl.
    rewrite IHl.
    trivial.
Qed.

(* On recommence la preuve à zéro pour voir un autre style de preuve *)
Goal forall l, l ++ [] = l.
Proof.
  
(* Preuve en utilisant le point virgule 'tac1 ; tac2' qui enchaine la tactique tac2 sur
   TOUS les sous-buts de tac1, on peut raccourcir la preuve *)
 induction l (*as [ |n l IHl]*); simpl; auto.
 rewrite IHl; trivial.
Qed.

(* On montre un contre-exemple de la commutativité de ++ *)
Lemma append_not_comm : (exists x y, x ++ y <> y ++ x).
Proof.
exists (1::[]).
exists (0::[]).
unfold not.
simpl.
intro H.
apply cons_injective in H.
destruct H.
inversion H.
Qed.

(**********************************************************************)
(* Exercice 2 : terminer les preuves suivantes                        *)
(**********************************************************************)

Lemma append_cons : forall (x y:list) a, a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Hint : utiliser discriminate pour les cas impossibles après induction sur l et sur l' *)
Lemma append_nil : forall l l':list, l ++ l' = [] -> l = [] /\ l' = [].
Proof.
  intros.
  destruct l.
  * split.
    - reflexivity.
    - simpl in H.
      assumption.
  * split.
    - discriminate.
    - simpl in H.
      destruct l'.
      + reflexivity.
      + discriminate.
(* NB : on remarque que destruct suffit : induction n'est pas nécessaire
   car les hypothèses d'induction ne sont pas utiles pour ce lemme *)
Qed.

(* Hint : utiliser rewrite avec l'hypothèse d'induction *)
Lemma append_assoc : forall l1 l2 l3, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  * simpl.
    intros.
    reflexivity.
  * simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(**********************************************************************)
(* FONCTION DE LONGUEUR DE LISTE                                      *)
(**********************************************************************)

(**********************************************************************)
(* Exercice 3 : compléter la fonction suivante qui calcule la         *)
(* longueur d'une liste et le lemme associé                           *)
(**********************************************************************)
Fixpoint length (l : list) : nat :=
  match l with
  | []     => 0 
  | x :: l => 1 + length l 
  end.

(* la preuve se fait ici simplement par calcul *)
Lemma example_length2 : length (1 :: 2 :: []) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma length_of_append : forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  * simpl.
    reflexivity.
  * simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(**********************************************************************)
(**********************************************************************)
(* POUR ALLER PLUS LOIN                                               *)
(**********************************************************************)
(**********************************************************************)

(**********************************************************************)
(* FONCTION MIRROIR                                                   *)
(**********************************************************************)

(**********************************************************************)
(* Exercice 4 : compléter la définition de la fonction miroir et      *)
(* terminer les preuves associées                                     *)
(**********************************************************************)

Fixpoint miroir l :=
  match l with
  | []     => [] (* todo *)
  | x :: l => miroir l ++ x::[]
  end.

Lemma example_rev1 : miroir (1 :: 2 :: 3 :: nil) = 3 :: 2 :: 1 :: nil.
Proof.
  auto.
Qed.

(* Hint : utiliser les lemmes précédents append_nil_r et append_assoc *)
Lemma miroir_append l1 l2 : miroir (l1 ++ l2) = (miroir l2) ++ (miroir l1).
Proof.
  intros.
  induction l1.
  * simpl.
    rewrite append_nil_r.
    reflexivity.
  * simpl.
    rewrite IHl1.
    rewrite append_assoc.
    reflexivity.
Qed.

(* Hint : utiliser le lemme miroir_append  *)
Lemma  miroir_miroir l : miroir (miroir l) = l.
Proof.
  intros.
  induction l.
  * simpl.
    reflexivity.
  * simpl.
    rewrite miroir_append.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.


(**********************************************************************)
(* CHARGEMENT DE LIBRAIRIE EXTERNE  *)
(**********************************************************************)

(* on va maintenant utiliser un lemme sur les entiers *)
(* https://coq.inria.fr/library/Coq.Arith.Plus.html *)
Require Import Arith.

(* on peut utiliser les commandes suivantes pour rechercher un théorème
   chargé dans Coq *)
Search (_ * (_ * _) = (_ * _) * _).
About  mult_assoc.

(**********************************************************************)
(* Exercice 5 : terminer les preuves suivantes  *)
(**********************************************************************)

(* Hint : cherchez le lemme de commutativité de l'addition sur les entiers pour le lemme suivant *)
Lemma length_of_rev : forall l, length (miroir l) = length l.
Proof.
  induction l as [ |n l IHl]; auto.
  simpl miroir.
  rewrite length_of_append .
  rewrite (IHl).
  apply plus_comm.
Qed.

End my_list.

(**********************************************************************)
(* LA BIBLIOTHEQUE STANDARD COQ DES LISTES *)
(**********************************************************************)

Section lists.

(* On importe la théorie des listes de la bibliothèque standard :
    https://coq.inria.fr/library/Coq.Lists.List.html
    https://github.com/coq/coq/blob/master/theories/Lists/List.v
*)

Require Import List.
Import ListNotations.

Variable A:Set.

(**********************************************************************)
(* Exercice 6 : terminer la preuve suivante  *)
(**********************************************************************)

(* Hint : cherchez des lemmes utiles dans la bibliothèque standard *)
Lemma list_cons_app_neq : forall (l l':list A), l' <> [] -> l' ++ l <> l.
Proof.
unfold not.
intros.
assert (l' ++ l = [] ++ l).
auto.
apply app_inv_tail in H1.
auto.
Qed.

End lists.
