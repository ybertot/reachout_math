Require Import List Arith Classical ClassicalEpsilon Lia.
Require Import Arith Lia.


Definition finite [T : Type] (s : T -> Prop) := 
  exists l : list T, forall x, s x -> In x l.



Definition Penum [T : Type] (s : T -> Prop) (l : list T) :=
 (forall x, s x -> In x l) /\
 (forall l',  (forall x, s x -> In x l') -> length l <= length l').

Definition enum [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits nil) (Penum s)).

Lemma enum_def: forall T : Type, forall s : T-> Prop, (exists l:list T,
((forall x, s x -> In x l) /\
 (forall l',  (forall x, s x -> In x l') -> length l <= length l')))->
(forall x, s x -> In x (enum s)) /\
 (forall l',  (forall x, s x -> In x l') -> length (enum s) <= length l').
Proof.
intros T s.
unfold enum.
apply (epsilon_spec(inhabits (nil : list T))).
Qed.

Definition odd (n : nat) := exists k, n = S (2 * k).

Definition even (n : nat) := exists k, n = 2 * k.

Lemma not_odd_equiv_even (n : nat) : ~(odd n <-> even n).
Proof.
Admitted.

Lemma not_odd_and_even (n : nat) : ~ (odd n /\ even n).
Proof.
induction n as [ | p Ih].
  intros [[x absx] _]; discriminate.
intros [[x xq] [y yq]].
destruct y as [ | y].
  discriminate.
replace (2 * S y) with (S (S (2 * y))) in yq by ring.
case Ih.
split.
exists y.
injection yq; intros H; rewrite H; ring.
exists x.
injection xq; intros H; rewrite H; ring.
Qed.

Lemma not_Penum_equal :
  not (forall (T : Type) (s1 s2 : T -> Prop) (x : T) (l : list T),
    s1 x <-> s2 x <-> (Penum s1 l <-> Penum s2 l)).
Proof.
intros abs.
assert (not_enum_odd : forall l, not (Penum odd l)).
intros l.
assert (exists y, odd y /\ ~ In y l) as [w [oddw wnotinl]].
  exists (S (list_max l * 2)).
  split.
   unfold odd.
   exists (list_max l); ring.
   intros s2min.
   assert (main : list_max l <= 2 * list_max l) by lia.
   assert (list_max l < S (list_max l * 2)) by lia.
   rewrite list_max_le in main.
   rewrite Forall_forall in main.
   apply main in s2min.
   lia.
intros [cover B].
apply cover in oddw.
case wnotinl.
assumption.
assert (not_enum_even : forall l, not (Penum even l)).
intros l.
assert (exists y, even y /\ ~ In y l) as [w [evenw wnotinl]].
  exists (S (list_max l) * 2).
  split.
   unfold even.
   exists (S (list_max l)); ring.
   intros s2min.
   assert (main : list_max l <= 2 * (list_max l)) by lia.
   rewrite list_max_le in main.
   rewrite Forall_forall in main.
   apply main in s2min.
   lia.
intros [cover B].
apply cover in evenw.
case wnotinl.
assumption.
destruct (abs nat odd even 0 nil) as [_ A].
assert (step1 : Penum odd nil <-> Penum even nil).
  split.
    intros [cover _].
    destruct (cover 1).
      exists 0; ring.
  intros [cover _].
    destruct (cover 0).
      exists 0; ring.
destruct (A step1) as [oddeven evenodd].
destruct evenodd.
exists 0; ring.
discriminate.
Qed.













