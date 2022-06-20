(* Preparatory work, not for the eyes of students. *)

Require Import Reals Coquelicot.Coquelicot Interval.Tactic Lra.

Open Scope R_scope.

Ltac Fix name := 
  match goal with
   | |- _ -> _ => fail "statement should be a universal quantification"
   | |- forall _, _ => intros n
   end.

Ltac assume f :=
  match goal with |- _ -> ?c =>
  let x := fresh "assumed_fact" in
  assert (x : f -> c);[intros x | exact x]
  end.

Ltac check := solve[auto | tauto | field; lra | lra | interval | nra ].

Ltac now_prove f := enough f by check.

Ltac derivative_prover := auto_derive; auto.

Lemma Mean_Value_Theorem :
   forall (f f' : R -> R) (a b : R),
   a < b /\ (forall c, a <= c <= b -> is_derive f c (f' c)) ->
   exists c, f b - f a = f' c * (b - a) /\ a < c < b.
Proof.
intros f f' a b [altb ff']; apply MVT_cor2; auto.
now intros c cint; rewrite <- is_derive_Reals; apply ff'.
Qed.

Lemma cos_decreasing x y :
  0 <= x <= PI /\ 0 <= y <= PI /\ x < y -> cos y < cos x.
Proof.
intros; apply cos_decreasing_1; tauto.
Qed.

Lemma cos_decreasing' x y :
 0 <= x <= PI /\ 0 <= y <= PI -> x < y <-> cos y < cos x.
Proof.
intros; split.
  apply cos_decreasing_1; tauto.
apply cos_decreasing_0; tauto.
Qed.

(* End of preparatory work. *)

Lemma sin_gt_x x : 0 < x -> sin x < x.
Proof.
Fail check.
assert (right_part : 1 < x -> sin x < x).
  assert (sin x <= 1)              by check.
  check.
enough (left_part : 0 < x <= 1 -> sin x < x)   by check.
assume (0 < x <= 1).
now_prove (sin x < x).
pose (f y := y - sin y).
assert (f 0 = 0).
    unfold f; rewrite sin_0.
    check.
enough (0 < f x)
    by (unfold f in *; check).
enough (0 < f x - f 0)
    by check.
assert (exists c, (f x - f 0 = (1 - cos c) * (x - 0)) /\
          0 < c < x) as [c main].
    apply Mean_Value_Theorem.
    assert (0 < x) by check.
  split.
    check.
  enough (derf : forall c : R, is_derive f c (1 - cos c)) by check.
      Fix c.
      unfold f; derivative_prover.
      check.
assert (f_equality : f x - f 0 = (1 - cos c) * (x - 0)) by check.
enough (0 < (1 - cos c) * (x - 0))
    by (rewrite f_equality; check).
enough (cos c < cos 0)
     by (rewrite cos_0 in *; check).
apply cos_decreasing'.
Fail check.
repeat split; try check.
interval_intro PI.
check.
Qed.

Section sum_n_first_natural_numbers.

Variable isnat : R -> Prop.

Hypothesis isnat0 : isnat 0.

Hypothesis isnat1 : isnat 1.

Hypothesis isnat_add : forall x y, isnat x /\ isnat y -> isnat (x + y).

Hypothesis isnat_ind : 
  forall P : R -> Prop,
    (P 0 /\
     (forall x, isnat x /\ P x -> P (x + 1))) ->
  forall x, isnat x -> P x.

Ltac prove_by_nat_induction := apply isnat_ind.

Variable sumn : R -> R.

Hypothesis sumn0 : sumn 0 = 0.

Hypothesis sumn_1 : forall n, sumn (n + 1) = sumn n + n.


Lemma sumn_eq : forall n, isnat n -> sumn n = n * (n - 1) / 2.
Proof.
prove_by_nat_induction.
assert (base_case : sumn 0 = 0 * (0 - 1) / 2).
    check.
assert (step_case : forall n, (isnat n /\ sumn n = n * (n - 1) / 2) ->
                    sumn (n + 1) = (n + 1) * ((n + 1) - 1) / 2).
        intros n facts.
        destruct facts as [n_is_nat eq_for_n].
        remember (sumn (n + 1)) as computation eqn: cval.
    assert (cval1 : computation = sumn n + n).
        rewrite cval, sumn_1; check.
    assert (cval2 : computation = (n * (n - 1) / 2 + n)).
        rewrite cval1, eq_for_n; check.
    check.
check.
Qed.



Section geometric_proof.

Variable finite : forall [T : Type], (T -> Prop) -> Prop.

Hypothesis finite_0 : forall [T : Type](s : T -> Prop),
  (forall x, ~ s x) <-> finite s.

Hypothesis finite_1 : forall [T : Type](x : T),
  finite (fun y => x = y).

Hypothesis finite_U : forall [T : Type](s1 s2 : T -> Prop),
  finite s1 /\ finite s2 -> finite (fun x => s1 x \/ s2 x).

Hypothesis eq_finite : forall [T : Type] (s1 s2 : T -> Prop),
  (forall x, s1 x <-> s2 x) -> (finite s1 <-> finite s2).

Variable bigop : forall [T T' : Type] (id0 : T')
  (op : T' -> T' -> T') (s : T -> Prop) (F : T -> T'), T'.

Variable card : forall [T : Type], (T -> Prop) -> R.

Variable nat_segment : R -> (R -> Prop).

Hypothesis nat_segment_def :
  forall n, 
  isnat n -> forall m, (nat_segment n m) <-> (m < n /\ isnat m).

Lemma isnat_ge0 x : isnat x -> 0 <= x.
Proof.
revert x; apply isnat_ind; split;[ lra | ].
intros x [_ it]; lra.
Qed.

Lemma nat_segment_0_empty : forall x, ~ nat_segment 0 x.
Proof.
intros x; rewrite nat_segment_def; auto.
intros [xlt0 natx]; assert (tmp := isnat_ge0 _ natx); lra.
Qed.

Lemma isnat_discrete x : isnat x ->
   forall y, isnat y -> x <= y < x + 1 -> x = y.
Proof.
revert x.
apply (isnat_ind (fun u => forall y, isnat y -> u <= y < u + 1 -> u = y)).
split.
apply (isnat_ind (fun u => 0 <= u < 0 + 1 -> 0 = u)).
  split;[auto | ].
  intros y [naty _] abs; assert (tmp := isnat_ge0 y naty); lra.
intros x [natx Ih].
apply (isnat_ind (fun y => x + 1 <= y < x + 1 + 1 -> x + 1 = y)).
split.
  assert (tmp := isnat_ge0 _ natx); lra.
intros y [naty _] cond.
enough (x = y) by lra.
apply Ih; auto; lra.
Qed.

Lemma nat_segment_step n : isnat n -> forall y,
  nat_segment (n + 1) y <-> nat_segment n y \/ y = n.
Proof.
intros natn y.
rewrite nat_segment_def; auto.
rewrite nat_segment_def; auto.
split.
  intros [yltxp1 naty].
  case (Rlt_dec y n) as [yltx | ygex].
    now left; split.
    right.
  now apply eq_sym; apply isnat_discrete; auto; lra.
intros [[yltx naty] | yisx].
  now split;[lra | auto].
now split;[lra | rewrite yisx; auto].
Qed.

Lemma finite_nat_segment n : isnat n -> finite (nat_segment n).
Proof.
revert n.
apply isnat_ind.
assert (finite (nat_segment 0)).
  now apply finite_0; apply nat_segment_0_empty.
assert (forall x, isnat x /\
           finite (nat_segment x) -> finite (nat_segment (x + 1))).
  intros x [natx Ih].
  apply (eq_finite _ _ (nat_segment_step x natx)); apply finite_U; split; auto.
  apply (eq_finite (fun y => x = y)).
    now intros y; split; intros one_eq; rewrite one_eq.
  now apply finite_1.
now split; auto.
Qed.

Class monoid (T : Type) (zero : T) (op : T -> T -> T) := {
  zero_neutral_l : forall x, op zero x = x;
  sero_neutral_r : forall x, op x zero = x;
  op_associative : forall x y z, op x (op y z) = op (op x y) z;
  op_commutative : forall x y, op x y = op y x
}.

Variable bigop_0 : forall [T T' : Type](zero : T') (op : T' -> T' -> T')
  (s : T -> Prop) (F : T -> T'),
  (forall x, ~ s x) -> bigop zero op s F = zero.

Variable bigop_rec: forall [T T' : Type](zero : T') (op : T' -> T' -> T')
   `{monoid T' zero op}
   (a : T) (s : T -> Prop) (F : T -> T'),
   (~ s a) ->
   bigop zero op (fun y => s y \/ y = a) F =
   op (bigop zero op s F) (F a).

Variable eq_set_bigop :
forall [T T' : Type](zero : T') (op : T' -> T' -> T')
   `{monoid T' zero op}
   (s1 s2 : T -> Prop) (F : T -> T'),
   (forall y, s1 y <-> s2 y) ->
   bigop zero op s1 F = bigop zero op s2 F.

Instance monoid_plus : monoid R 0 Rplus.
Proof.
constructor.
  exact Rplus_0_l.
  exact Rplus_0_r.
  exact (fun x y z => eq_sym (Rplus_assoc x y z)).
  exact Rplus_comm.
Qed.

Lemma sumn_bigop n :  isnat n ->
  sumn n = bigop 0 Rplus (nat_segment n) (fun i => i).
Proof.
revert n; apply isnat_ind.
assert (sumn 0 = bigop 0 Rplus (nat_segment 0) (fun i => i)).
  rewrite sumn0.
  now rewrite bigop_0; auto; apply nat_segment_0_empty.
assert(forall x,
   isnat x /\ sumn x = bigop 0 Rplus (nat_segment x) (fun i : R => i) ->
   sumn (x + 1) = bigop 0 Rplus (nat_segment (x + 1)) (fun i : R => i)).
intros x [natx Ih].
  rewrite (eq_set_bigop 0 Rplus (nat_segment (x + 1))
             (fun y => nat_segment x y \/ y = x)
             (fun i => i) (nat_segment_step x natx)).
  rewrite bigop_rec.
      now rewrite sumn_1, Ih.
    typeclasses eauto.
  rewrite nat_segment_def; auto; intros [xltx _]; lra.
tauto.
Qed.
