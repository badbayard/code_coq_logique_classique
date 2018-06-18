Require Import Utf8.

(* On introduit les variables avec lesquelles on va travailler par la suite *)
Variables P Q R: Prop.

(* La preuve vue en cours, à dérouler pas à pas *)
Theorem application: P -> ((P -> Q) -> Q).
Proof.
  intro HP.
  intro HPQ.
  apply HPQ.
  exact HP.
  Restart.
  auto.
Qed.

(**********************************************************************)
(* Exercice 1 *)

(* Compléter la preuve de l'exercice 1 *)
Theorem exercice_1: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intro HPQ.
  intro HQR.
  intro HP.
  apply HQR.
  apply HPQ.
  exact HP.
  Restart.
  (* en donnant ici le terme de preuve (de la composition) *)
  exact (fun f g x => g(f(x))).
Qed.

(* Une variante de la précédente avec /\ *)
Theorem execice_1b: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
  intro HPQR.
  destruct HPQR.
  intro HP.
  apply H0.
  apply H.
  exact HP.
  (* ou: *)
  Restart.
  intro HPQR.
  elim HPQR.
  apply exercice_1.
Qed.

(**********************************************************************)
(* Exercice 2 *)

(* Généralisation du passage de l'exercice 1 à l'exercice 1b *)
(* Cela peut également s'écrire (P -> Q -> R) <-> (P /\ Q -> R) *)
(* Ce théorème est lié à la curryfication vue en LIFAP5 *)
(* Utiliser la tactique split pour traiter un /\ à démontrer. *)
Theorem exercice_2: ((P -> Q -> R) -> (P /\ Q -> R)) /\ ((P /\ Q -> R) -> (P -> Q -> R)) .
Proof.
  split.
* intros HPQR HPQ.
  destruct HPQ.
  apply HPQR; assumption.
  (* fin du premier sens *)
* intros HPQR HP HQ.
  apply HPQR.
  split; assumption.
Qed.

Theorem exercice_2b: (P -> Q) /\ (P -> R) <-> (P -> Q /\ R).
Proof.
  split.
  * intro HCj.
    intro HP.
    destruct HCj as [HPQ HPR].
    split.
    + apply HPQ.
      exact HP.
    + apply HPR.
      exact HP.
  (* fin du premier sens *)
  * intro HPQR.
    split; intro HP; apply HPQR; assumption.
    (* ou plus explicite,, sans utiliser ';'
    + intro HP.
      apply HPQR.
      assumption.
    + intro HP.
      apply HPQR.
      assumption. *)
  Restart.
  tauto.
  Show Proof. (* le terme de preuve *)
Qed.

Theorem exemple_avec_items_reset_et_pt_virg: P /\ Q -> P /\ Q.
Proof.
  intro HPQ.
  split.
  * elim HPQ.
    intro HP.
    intro HQ.
    assumption.
  * elim HPQ.
    intro HP.
    intro HQ.
    assumption.
  Restart.
  intro HPQ.
  split; elim HPQ; intros HP HQ; assumption.
  Restart.
  (* avec la tactique Destruct au lieu de elim qui ne modifie pas le but *)
  intro HPQ; destruct HPQ; split; assumption.
  Restart.
  (* ou directement avec exact *)
  intro H; exact H.
  Restart.
  exact (fun x => x). 
Qed.

(**********************************************************************)
(* Exercice 3 *)

Definition Tiers_exclus (P:Prop):Prop := P \/ ~P.

(* Utilisation du tiers exclus pour montrer *)
Theorem De_Morgan_1: (Tiers_exclus P) ->  (~(P /\ Q) <-> ~P \/ ~Q).
Proof.
  unfold Tiers_exclus .
  intro PNP.
  split.
  + intro NPQ.
    destruct PNP.
    * right.
      intro HQ.
      apply NPQ.
      split; assumption.
    * left.
      assumption.
  + intro NPNQ.
    intro PQ.
    destruct NPNQ.
    * destruct PQ as [HP HQ].
      contradiction.
      (*ou explicitement apply H; assumption.*)
    * apply H.
      destruct PQ as [HP HQ].
      assumption.
Qed.

Theorem Pierce: (Tiers_exclus P) -> ((P -> Q) -> P) -> P.
Proof.
  unfold Tiers_exclus.
  intros PNP PQP.
  destruct PNP.
  *  assumption.
  *  apply PQP.
     intro HP.
     contradiction.
Qed.
