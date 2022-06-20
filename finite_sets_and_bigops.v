Require Import List Arith Classical ClassicalEpsilon.

Definition finite [T : Type] (s : T -> Prop) := 
  exists l : list T, forall x, s x -> In x l.

Lemma finite_0 [T : Type] (s0 : T -> Prop) :
  (forall x, ~s0 x) -> finite s0.
Proof.
now intros char_empty; exists nil; intros x xinempty; case (char_empty x).
Qed.

Lemma finite_add_elem [T : Type] (s : T -> Prop) (a : T) :
  finite s <-> finite (fun x =>  s x \/ x = a).
Proof.
split; intros [l char_sl].
  exists (a :: l); intros x [xins | xisa].
    now simpl; right; apply char_sl.
  now simpl; rewrite xisa; left.
now exists l; intros x xins; apply char_sl; left.
Qed.


Definition card [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits 0)
     (fun n : nat =>
        (exists l,  (forall x, s x -> In x l) /\ n = length l) /\
        (forall l, (forall x, s x -> In x l) -> n <= length l))).
Search epsilon.
Lemma card_def: forall T : Type, forall s : T-> Prop, (exists n:nat,
 (exists l,  (forall x, s x -> In x l) /\ n = length l) /\
        (forall l, (forall x, s x -> In x l) -> n <= length l))-> 
(exists l,  (forall x, s x -> In x l) /\ card s = length l) /\
        (forall l, (forall x, s x -> In x l) -> card s <= length l).
Proof.
intros T s.
Fail apply epsilon_spec.
unfold card.
apply (epsilon_spec(inhabits 0)).
Qed.
About epsilon_spec .
(* Je pense que la preuve suivante sera nécessaire pour montrer que le
  cardinal est bien défini pour tous les ensembles finis. *)

Lemma card_0[T: Type]: forall s: T-> Prop, ( forall x ,~s x)-> card s = 0.
  Proof.

  Admitted.

Lemma finite_has_minimal_list [T : Type] (s : T -> Prop) :
  finite s <-> (exists l, (forall x, s x -> In x l) /\ 
                (forall l',  (forall x, s x -> In x l') -> 
                    length l <= length l')).
Admitted.

Definition enum [T : Type] (s : T -> Prop) :=
  epsilon (inhabits nil)
    (fun l : list T => 
       (exists l, (forall x, s x -> In x l) /\ 
                (forall l',  (forall x, s x -> In x l') -> 
                    length l <= length l'))).

Lemma finite_enum_card [T : Type] (s : T -> Prop) :
  finite s -> card s = length (enum s).
Proof.




