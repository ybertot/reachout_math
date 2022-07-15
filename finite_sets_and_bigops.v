Require Import List Arith Classical ClassicalEpsilon Lia.

Section FiniteSetOperation.
Definition finite [T : Type] (s : T -> Prop) := 
  exists l : list T, forall x, s x -> In x l.

Definition singleton [T : Type](x:T) :=
  fun y => y=x.
Definition union[T : Type] (s1 s2:T -> Prop) :=
    fun x => s1 x \/ s2 x.
Definition intersection [T : Type] (s1:T -> Prop)(s2:T -> Prop) :=
    fun x => s1 x /\ s2 x.
Definition compl [T : Type] (s : T -> Prop)(x : T) :=
  not(s x).
Lemma union_comm [T : Type] (s1 s2:T -> Prop):
forall x:T ,(union s1 s2) x  <->(union s2 s1)x .
Proof.
intros x.
apply (or_comm (s1 x) (s2 x)) .
Qed.

Lemma intersection_comm[T : Type] ( s1 s2 : T -> Prop) :
forall x : T, (intersection s1 s2) x <-> (intersection s2 s1) x.
Proof.
unfold intersection.
intros x.
apply (and_comm (s1 x)(s2 x)).
Qed.

Lemma finite_0 [T : Type] (s0 : T -> Prop) :
  (forall x, ~s0 x) -> finite s0.
Proof.
now intros char_empty; exists nil; intros x xinempty; case (char_empty x).
Qed.

Lemma finite_singleton [T: Type](a : T) :
  finite (singleton a).
Proof.
unfold singleton.
unfold finite.
exists (a::nil); intros x H.
simpl; auto.
Qed.

Lemma Union_preserves_Finite [T : Type](s1 : T -> Prop)(s2 : T -> Prop):
(finite s1 /\ finite s2)  <-> finite (union s1 s2).  
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

Lemma Intersection_preserves_Finite [T : Type](s1 s2 : T -> Prop):
(finite s1 \/ finite s2)  -> finite (intersection s1 s2).
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

End FiniteSetOperation.

Section Cardinal.
Definition Pcard [T : Type] (s : T -> Prop) (n : nat) :=
 (exists l, (forall x, s x -> In x l) /\ n = length l) /\
 (forall l, (forall x, s x -> In x l) -> n <= length l).

Definition card [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits 0) (Pcard s)).

Lemma card_def: forall [T : Type] (s : T -> Prop),
  (exists n, Pcard s n) -> Pcard s (card s).
(*
Lemma card_def: forall T : Type, forall s : T-> Prop, (exists n:nat,
 (exists l,  (forall x, s x -> In x l) /\ n = length l) /\
        (forall l, (forall x, s x -> In x l) -> n <= length l))-> 
(exists l,  (forall x, s x -> In x l) /\ card s = length l) /\
        (forall l, (forall x, s x -> In x l) -> card s <= length l).
*)
Proof.
intros T s.
apply epsilon_spec.
Qed.
About epsilon_spec .

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
destruct (card_def _ (ex_intro _ 0 cards0)) as [_ min].
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

Lemma Pcard_card [T : Type](s : T -> Prop):
forall n, Pcard s n -> card s = n.
Proof.
intros n pcards.
destruct pcards as [[L H] H'].
destruct H as [Ih len].
assert (fs : finite s ).
exists L; auto.
assert (card_tmp := finite_Pcard s fs ).
assert (tmp := card_def _ card_tmp).
destruct tmp as [[L' [tmpH1 tmpH1']] tmpH2].
apply tmpH2 in Ih.
apply H' in tmpH1.
lia.
Qed.

End Cardinal.

Section Enumeration.
Definition Penum [T : Type] (s : T -> Prop) (l : list T) :=
 (forall x, s x -> In x l) /\
 (forall l',  (forall x, s x -> In x l') -> length l <= length l').

Definition enum [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits nil) (Penum s)).

Lemma enum_def: forall [T : Type](s : T-> Prop),
(exists l:list T, Penum s l) -> Penum s (enum s). 
(*(exists l:list T,
((forall x, s x -> In x l) /\
 (forall l',  (forall x, s x -> In x l') -> length l <= length l')))->
(forall x, s x -> In x (enum s)) /\
 (forall l',  (forall x, s x -> In x l') -> length (enum s) <= length l').*)
Proof.
intros T s.
unfold enum.
apply epsilon_spec.
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
assert (tmp := card_def _ card_tmp).
assert (enum_tmp := fs).
rewrite (finite_has_minimal_list s ) in enum_tmp.
assert (tmp' := enum_def _ enum_tmp).
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
assert (tmp' := enum_def _ enum_tmp).
destruct tmp' as [tmpH1' tmpH2'].
destruct (remove_elem x (enum s) H) as [l1 Pl1].
case (classic (s x)); auto.
intros nsx.
assert (sincludedl1 : forall y: T , s y -> In y l1).
intros y sy.
assert (tmp := elem_removed_in x l1 (enum s) y Pl1 (tmpH1' y sy)).
destruct tmp as [yx | It ]; auto.
case ( nsx ).
rewrite <- yx ;auto.
apply tmpH2' in sincludedl1.
assert (tmpl := remove_length x l1 (enum s) Pl1).
lia.
Qed.

Lemma Penum_finite[T : Type](s : T -> Prop)(l : list T):
Penum s l -> finite s.
Proof.
intros ensl; exists l.
destruct ensl as [H H0].
exact H.
Qed.

(*
Lemma Penum_equal [T : Type](s1 s2 : T -> Prop)(x : T)(l : list T):
 (s1 x<->s2 x) <-> (Penum s1 l <-> Penum s2 l). is wrong.We can see the details in
counterexemple.v
*)
End Enumeration.

Section FiniteSetFacts.
Lemma card_not_0_has_elem [T : Type](s : T -> Prop):
finite s -> card s <> 0 -> exists a : T , s a.
Proof.
intros fs H.
assert(th := finite_enum_card s fs).
assert (Hfei := finite_enum_included s fs).
destruct (enum s ) as [| a tl].
rewrite th in H.
easy.
exists a.
apply Hfei.
simpl.
left.
easy.
Qed.

Lemma card_add_elem [T : Type] (s : T -> Prop) (a : T):
  finite s -> ~ s a -> card (union (singleton a) s ) = card s + 1.
Proof.
intros fs ans.
assert (tmp := finite_Pcard s fs).
assert (tmp' := card_def _ tmp).
assert (card_add := (card_s s _ a tmp' ans)).
replace (card s + 1) with (S (card s)) by ring.
apply Pcard_card.
exact card_add.
Qed.

Lemma card_inter_compl [T : Type] (s : T -> Prop) (a : T):
 s a -> card (intersection s (compl (singleton a)) )= card s -1.
Admitted.


Lemma card_union [T : Type] (s1 s2 : T -> Prop) :
  finite s1 -> finite s2 ->
  card (union s1 s2) = card s1 + card s2 - card (intersection s1 s2).
Proof.
Admitted.
End FiniteSetFacts.




