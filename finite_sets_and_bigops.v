Require Import List Arith Classical ClassicalEpsilon Lia.


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

Definition Pcard [T : Type] (s : T -> Prop) (n : nat) :=
 (exists l, (forall x, s x -> In x l) /\ n = length l) /\
 (forall l, (forall x, s x -> In x l) -> n <= length l).

Definition card [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits 0) (Pcard s)).

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
intros s sempty.
assert (cards0 : Pcard s 0).
  split.
    exists nil.
    split.
      now intros x sx; case (sempty x).
    easy.
  intros l _; apply Nat.le_0_l.
destruct (card_def _ _ (ex_intro _ 0 cards0)) as [_ min].
enough (cle0 : card s <= 0) by now apply eq_sym; apply le_n_0_eq.
now change 0 with (length (@nil T)); apply min; intros x sx; case (sempty x).
Qed.

Inductive elem_removed [T : Type] (x : T) : list T -> list T -> Prop :=
  remove_one : forall l, elem_removed x l (x :: l)
| remove_extra : forall y l1 l2, 
   elem_removed x l1 l2 ->
   elem_removed x (y :: l1) (y :: l2).

Lemma remove_elem [T : Type] (x : T) (l : list T) :
  In x l -> exists l1, elem_removed x l1 l.
Proof.
induction l as [ | y l' Ih].
  easy.
simpl; intros [yisx | yinl'].
  exists l'; rewrite yisx; apply remove_one.
destruct (Ih yinl') as [l2 Pl2].
now exists (y :: l2); apply remove_extra.
Qed.

Lemma remove_length [T : Type] (x : T) (l1 l2 : list T) :
  elem_removed x l1 l2 -> length l2 = S (length l1).
Proof.
induction 1 as [ | a l1 l2 erl1l2 Ih];[easy | ].
now simpl; rewrite Ih.
Qed.

Lemma elem_removed_in [T : Type] (x : T) (l1 l2 : list T) (y : T) :
  elem_removed x l1 l2 ->
  In y l2 -> y = x \/ In y l1.
Proof.
induction 1 as [ | a l1 l2 erl1l2 Ih].
  simpl; intros [yisx | yinl1];[now left; rewrite yisx | now right].
simpl; intros [aisy | ainl2].
  now right; left.
destruct (Ih ainl2) as [yisx | yinl1].
  now left.
now right; right.
Qed.

Lemma card_s[T: Type]: forall s: T-> Prop, forall n, forall x : T,
  Pcard s n ->
  ~s x -> Pcard (fun y => y = x \/ s y) (S n).
Proof.
intros s n x cardsn xout.
destruct cardsn as [[wl [wlin wls]] minc].
split.
  exists (x :: wl); split.
    now intros y [yisx | sy]; simpl;[left | right]; auto.
  now simpl; rewrite <-wls.
intros l lcovers.
assert (xinl : In x l).
  now apply lcovers; left.
destruct (remove_elem x l xinl) as [l' Pl'].
rewrite (remove_length _ _ _ Pl').
apply le_n_S.
apply minc.
intros y sy.
assert (yl : In y l).
  now apply lcovers; right.
destruct (elem_removed_in _ l' _ y Pl' yl) as [yisx | yinl'];[ | easy].
case xout.
now rewrite <- yisx.
Qed.

Lemma finite_Pcard [T : Type] (s : T -> Prop) :
  finite s -> exists n, Pcard s n.
Proof.
intros [l Pl]; revert s Pl.
induction l as [ | a l' Ih].
  intros s empty.
    exists 0.
  split.
    exists nil; split;[ | easy].
    assumption.
  now intros l _; apply le_0_n.
simpl.
intros s ssub.
pose (s' := fun x => s x /\ x <> a).
assert (s'sub : forall x, s' x -> In x l').
  intros x s'x.
  assert (sx : s x) by now destruct s'x.
  destruct (ssub _ sx) as [aisx | xinl]; auto.
  now rewrite <- aisx in s'x; destruct s'x as [_ abs]; case abs.
destruct (Ih s' s'sub) as [n' [[wl [s'subw n'w]] min']].
case (classic (s a)) as [sa | ans].
  exists (S n').
  split.
    exists (a :: wl).
    split.
      intros x sx.
      case (classic (x = a)) as [xisa | xna].
        now simpl; rewrite xisa; auto.
      simpl; right.
      apply s'subw.
      now split; auto.
    now simpl; rewrite n'w.
  intros l ssubl.
  assert (exists l2,  elem_removed a l2 l) as [l2 Pl2].
    apply remove_elem.
    apply ssubl.
    exact sa.
  assert (Pl2' := Pl2).
  apply remove_length in Pl2.
  assert (minl2 : n' <= length l2).
    apply min'.
    intros x [sx xna].
    apply (elem_removed_in _ _ _ x) in Pl2'.
      destruct Pl2' as [xisa | xinl2].
        now case xna.
      easy.
    now apply ssubl; apply sx.
  lia.
exists n'.
assert (ss' : forall x, s x -> s' x).
  intros x sx; split;[easy | ].
  now intros xisa; rewrite xisa in sx; case ans.
split.
  exists wl.
  split;[ | easy].
  intros x sx; apply s'subw.
  now apply ss'.
intros l ssubl.
apply min'.
intros x s'x; apply ssubl.
now destruct s'x.
Qed.

Lemma Union_preserves_Finite [T : Type](s1 : T -> Prop)(s2 : T -> Prop):
(finite s1 /\ finite s2)  <-> finite (fun x =>  s1 x \/ s2 x ).  
Proof.
split.
  intros [f1 f2].
  unfold finite in *.
  destruct f1 as [LIh1 H1].
  destruct f2 as [LIh2 H2].
    exists (LIh1++LIh2).
    intros x H'.
      destruct H'.
    apply (in_or_app LIh1 LIh2 x) ;left ;apply H1;exact H.
  apply (in_or_app LIh1 LIh2 x) ;right ;apply H2;exact H.
intros [L Ih].
  unfold finite in *.
    split;exists L; intros x H; apply Ih.
  left; exact H.
right; exact H.
Qed.


Lemma Intersection_preserves_Finite [T : Type](s1 : T -> Prop)(s2 : T -> Prop):
(finite s1 \/ finite s2)  -> finite (fun x =>  s1 x /\ s2 x ).
Proof.
intros.
unfold finite in *.
destruct H.
destruct H as [L1 Ih1];exists L1;intros x [H1 H2];apply Ih1;exact H1.
destruct H as [L2 Ih2];exists L2;intros x [H1 H2];apply Ih2;exact H2.
Qed.

Lemma Subset_Finite [T : Type] (s s' : T -> Prop) :
 (forall x, s' x -> s x) ->( finite s -> finite s') .
Proof.
intros Hsubset Hf.
unfold finite in *.
destruct Hf as [L Ih].
exists L.
intros.
apply Ih.
apply Hsubset.
exact H.
Qed.

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



Lemma finite_has_minimal_list [T : Type] (s : T -> Prop) :
  finite s <-> exists l, Penum s l.
Proof.
assert (right_to_left : (exists l, (forall x, s x -> In x l) /\ 
                (forall l',  (forall x, s x -> In x l') -> 
                    length l <= length l')) -> finite s).
  intros [l Pl].
  destruct Pl as [Pl1 _].
  exists l; exact Pl1.
split;[ | auto].
clear right_to_left.
intros fs.
assert (tmp := finite_Pcard s fs).
unfold Pcard in tmp.
destruct tmp as [n [Htmp1 Htmp2]].
destruct Htmp1 as [L H1].
exists L.
destruct H1 as [fL nth].
unfold Penum.
rewrite <-nth.
auto.
Qed.

Lemma finite_enum_card [T : Type] (s : T -> Prop) :
  finite s -> card s = length (enum s).
Proof.
intros fs.
assert (card_tmp := finite_Pcard s fs).
assert (tmp := card_def _ _ card_tmp).
assert (enum_tmp := fs).
rewrite (finite_has_minimal_list s ) in enum_tmp.
assert (tmp' := enum_def _ _ enum_tmp).
destruct tmp as [tmpH1 tmpH2].
destruct tmpH1 as [L Ih1].
destruct Ih1 as [null H_card].
destruct tmp' as [tmpH1' tmpH2'].
apply tmpH2 in tmpH1'.
apply tmpH2' in null.
rewrite <- H_card in null.
auto with arith.
Qed.

Lemma finite_enum_included [T : Type](s : T -> Prop):
  finite s -> (forall x, In x (enum s) -> s x).
Proof.
intros fs x H.
assert (enum_tmp := fs).
rewrite (finite_has_minimal_list s ) in enum_tmp.
assert (tmp' := enum_def _ _ enum_tmp).
destruct tmp' as [tmpH1' tmpH2'].
assert (th := finite_enum_card s fs).
destruct fs as [L Ih].
apply tmpH2' in Ih.
rewrite <-th in Ih.

Admitted.






