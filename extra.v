Require Import List.

Fixpoint merge (l1 l2: list nat) : list nat :=
  match l1, l2 with
  | _, nil => l1
  | nil, _ => l2
  | h1::r1, h2::r2 => if Nat.leb h1 h2 then h1::h2::(merge r1 r2) 
                                       else h2::h1::(merge r1 r2)
  end.

Fixpoint split (l : list nat) : (list nat)*(list nat) :=
  match l with
  | nil => (nil, nil)
  | h::nil => (l, nil)
  | h1::h2::r => match (split r) with
                 | (l1, l2) => (h1::l1, h2::l2)
                 end
  end.


Theorem sorted_red: forall (n:nat) (l: list nat), sorted(n::l) -> sorted l.
Proof.
 intros n l H.
 inversion H. apply sorted0. assumption.
Qed.



Eval compute in (split (1::2::3::4::5::nil)).
