(* Trial division for primes small enough that walking up to the square root
   is a trivial computation.  Larger Pasta factors are certified in
   [Pocklington.v]; this file only has to be sound. *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* [odd_trial n d steps] is true when [n] has no divisor in the arithmetic
   progression [d], [d+2], ... that is at most [sqrt n].  [steps] bounds the
   walk; [primeb] supplies enough of them to reach past [sqrt n]. *)
Fixpoint odd_trial (n d : Z) (steps : nat) : bool :=
  match steps with
  | O => true
  | S steps' =>
      if n <? d * d then true
      else if n mod d =? 0 then false
      else odd_trial n (d + 2) steps'
  end.

Definition primeb (n : Z) : bool :=
  if n <=? 1 then false
  else if n =? 2 then true
  else if n mod 2 =? 0 then false
  else odd_trial n 3 (Z.to_nat (Z.sqrt n)).

Lemma mod2_add2 (d : Z) : (d + 2) mod 2 = d mod 2.
Proof.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_same by lia.
  rewrite Z.add_0_r.
  apply Z.mod_mod; lia.
Qed.

Lemma odd_trial_sound n d steps :
  d mod 2 = 1 ->
  0 < d ->
  odd_trial n d steps = true ->
  forall k,
    d <= k < d + 2 * Z.of_nat steps ->
    k mod 2 = 1 ->
    k * k <= n ->
    n mod k <> 0.
Proof.
  revert d.
  induction steps as [|steps IH]; intros d Hmod2 Hdpos Htrue k Hk Hkodd Hsq.
  - lia.
  - simpl in Htrue.
    destruct (Z.ltb_spec n (d * d)) as [Hlt|Hge].
    + assert (d * d <= k * k) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
    + destruct (Z.eqb_spec (n mod d) 0) as [Hzero|Hnz].
      * discriminate.
      * assert (k = d \/ k = d + 1 \/ d + 2 <= k) by lia.
        destruct H as [->|[->|Hkge]].
        -- exact Hnz.
        -- exfalso.
           assert (E1 : 1 mod 2 = 1) by (apply Z.mod_small; lia).
           assert ((d + 1) mod 2 = 0).
           { rewrite Z.add_mod by lia. rewrite Hmod2, E1. reflexivity. }
           lia.
        -- apply IH with (d := d + 2).
           --- rewrite mod2_add2. exact Hmod2.
           --- lia.
           --- exact Htrue.
           --- lia.
           --- exact Hkodd.
           --- exact Hsq.
Qed.

(* A composite number has a factor [k] with [1 < k] and [k * k <= n].
   If [n] is odd that factor is odd and at least 3, so the trial walk sees it. *)
Lemma no_odd_divisor_prime n :
  1 < n ->
  n mod 2 <> 0 ->
  (forall k, 3 <= k -> k mod 2 = 1 -> k * k <= n -> n mod k <> 0) ->
  Z.prime n.
Proof.
  intros Hn Hodd Hall.
  split; [exact Hn|].
  intros d Hd Hdiv.
  assert (0 < d) by lia.
  assert (Hn' : n = d * (n / d)).
  { apply (proj2 (Z.div_exact n d ltac:(lia))).
    apply (proj2 (Z.mod_divide n d ltac:(lia))). exact Hdiv. }
  set (m := n / d) in *.
  assert (Hm : 1 < m < n) by nia.
  set (k := Z.min d m).
  assert (Hk : 1 < k /\ k * k <= n /\ (k | n)).
  { unfold k. destruct (Z_le_dec d m) as [Hdm|Hmd].
    - rewrite (Z.min_l d m Hdm).
      split; [lia|]. split.
      + rewrite Hn'. apply Z.mul_le_mono_nonneg; lia.
      + exact Hdiv.
    - assert (Hmdle : m <= d) by lia. rewrite (Z.min_r d m Hmdle).
      split; [lia|]. split.
      + rewrite Hn'. apply Z.mul_le_mono_nonneg; lia.
      + exists d. exact Hn'. }
  assert (Hkodd : k mod 2 = 1).
  { destruct (Z.eq_dec (k mod 2) 0) as [Hk0|Hk1].
    - exfalso.
      assert (H2k : (2 | k)).
      { apply (proj1 (Z.mod_divide k 2 ltac:(lia))). exact Hk0. }
      destruct Hk as [_ [_ Hkdiv]].
      assert (H2n : (2 | n)) by (eapply Z.divide_trans; eauto).
      apply Hodd. apply (proj2 (Z.mod_divide n 2 ltac:(lia))). exact H2n.
    - pose proof (Z.mod_pos_bound k 2 ltac:(lia)). lia. }
  assert (Hkn0 : n mod k = 0).
  { apply (proj2 (Z.mod_divide n k ltac:(lia))). tauto. }
  assert (Hk3 : 3 <= k).
  { assert (k <> 2) by (intros ->; lia). lia. }
  assert (Hneq : n mod k <> 0).
  { apply Hall; try lia; tauto. }
  congruence.
Qed.

Theorem primeb_prime n : primeb n = true -> Z.prime n.
Proof.
  unfold primeb.
  destruct (Z.leb_spec n 1) as [Hle|Hgt].
  - discriminate.
  - destruct (Z.eqb_spec n 2) as [->|Hneq].
    + intros _. exact Z.prime_2.
    + destruct (Z.eqb_spec (n mod 2) 0) as [Heven|Hodd].
      * discriminate.
      * intros Htrial.
        apply no_odd_divisor_prime; [lia| exact Hodd|].
        intros k Hk3 Hmod Hsq.
        pose (s := Z.sqrt n).
        pose proof (Z.sqrt_spec n ltac:(lia)) as Hspec.
        change (s * s <= n < Z.succ s * Z.succ s) in Hspec.
        assert (k <= s) by nia.
        assert (Z.of_nat (Z.to_nat s) = s).
        { apply Z2Nat.id. apply Z.sqrt_nonneg. }
        apply odd_trial_sound with (d := 3) (steps := Z.to_nat s).
        all: try (exact Htrial); try (exact Hmod); try (exact Hsq);
             try reflexivity; lia.
Qed.
