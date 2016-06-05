(* ******************** *)
(* Aussagenlogik in Coq *)
(* ******************** *)

(* Transitivität der Implikation *)

Theorem imp_trans: forall P Q R: Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
 intros P Q R.
 intros H0 H1.
 intro.
 apply H1.
 apply H0.
 assumption.
 Show Proof.
Qed.

(* Distributivität von "oder" "\/" und "und" "\/" *)

Theorem or_distrib: forall P Q R: Prop, (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
Proof. 
 intros P Q R.
 intro H.
 destruct H as [ HPQ | HR ].
  split.
   Check proj1.
   left. apply proj1 with (B:=Q). assumption.
   left. apply proj2 with (A:=P). assumption.
  split.
   right. assumption.
   right. assumption.
 Show Proof.
Qed.

(* nochmal, jetzt mit automatischem Beweis *)

Theorem or_distrib': forall P Q R: Prop, (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
Proof.
 tauto.
 Show Proof.
Qed.

(* *************** *)
(* Abhängige Typen *)
(* *************** *)


(* ******************* *)
(* einfache Arithmetik *)
(* ******************* *)

Require Mult.

Lemma times2: forall n: nat, n+n=2*n.
Proof.
 intro n.
 induction n.
  reflexivity.
  Search (S _ + _).
  rewrite plus_Sn_m.
  Search (_ + _ = _ + _).
  rewrite PeanoNat.Nat.add_comm.
  rewrite plus_Sn_m.
  rewrite IHn.
  Search ( (_*S _) =_).
  rewrite PeanoNat.Nat.mul_succ_r.
  rewrite PeanoNat.Nat.add_comm.
  simpl.
  reflexivity.
Qed.

Theorem binom1: forall a b: nat, (a+b)*(a+b) = a*a + 2*a*b +b*b.
Proof.
 intros.
 Search ( (_+_)*_ ).
 rewrite PeanoNat.Nat.mul_add_distr_r.
 rewrite PeanoNat.Nat.mul_add_distr_l.
 rewrite PeanoNat.Nat.mul_add_distr_l.
 Search ( _*_ = _*_).
 rewrite PeanoNat.Nat.mul_comm with (n:=b).
 Search ( _ + (_+_) ).
 rewrite <- Plus.plus_assoc_reverse.
 Search (_+_ = _).
 rewrite PeanoNat.Nat.add_cancel_r with (p:=b*b).
 rewrite <- times2.
 rewrite PeanoNat.Nat.mul_add_distr_r.
 rewrite <- Plus.plus_assoc_reverse.
 reflexivity.
 Show Proof.
Qed.

Require Import Ring.
Require Import ArithRing.

Theorem binom1': forall a b: nat, (a+b)*(a+b) = a*a + 2*a*b +b*b.
Proof.
 intros.
 ring.
 Show Proof.
Qed.


(* ********************* *)
(* Beweisbares Sortieren *)
(* ********************* *)




