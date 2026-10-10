(* Pocklington's criterion, in the two forms used for the Pasta primes.

   If [n - 1] has a divisor [F] with [F * F >= n], where [F] is a prime
   ([pocklington1]) or a product of two distinct primes ([pocklington2]),
   and a base [a] satisfies [a^(n-1) ≡ 1 (mod n)] together with
   [gcd(a^((n-1)/q) - 1, n) = 1] for every prime [q] dividing [F], then [n]
   is prime.  The powers are [Zmod.pow], so a certificate is a handful of
   [vm_compute] goals. *)

From Stdlib Require Import ZArith Zmod Lia.
From Pasta Require Import Trial.
Local Open Scope Z_scope.

Lemma zmod_eqb_true [m] (x y : Zmod m) :
  Zmod.eqb x y = true -> x = y.
Proof.
  intro H. destruct (Zmod.eqb_spec x y); [exact H0| discriminate].
Qed.

Lemma div_exact_quotient (a b : Z) :
  b <> 0 -> (b | a) -> a = b * (a / b).
Proof.
  intros Hb Hdiv.
  apply (proj2 (Z.div_exact a b Hb)).
  apply (proj2 (Z.mod_divide a b Hb)). exact Hdiv.
Qed.

(* A proper factor of [n], or a proof that [n] is prime.  The search is by
   induction on a fuel counter equal to [n - start] and is never executed;
   the Pasta certificates go through Pocklington instead. *)
Lemma factor_search_fuel (fuel : nat) (n start : Z) :
  Z.to_nat (n - start) = fuel ->
  1 < n -> 1 < start <= n ->
  {d | start <= d < n /\ (d | n)} +
  {forall d, start <= d < n -> ~ (d | n)}.
Proof.
  revert n start.
  induction fuel as [|fuel IH]; intros n start Hfuel Hn Hstart.
  - right. intros d Hd.
    destruct (Z_le_gt_dec (n - start) 0) as [Hle|Hgt].
    + lia.
    + assert (Hpos : 0 < n - start) by lia.
      assert (Hnn : 0 <= n - start) by lia.
      apply (proj1 (Z2Nat.inj_lt 0 (n - start) (Z.le_refl 0) Hnn)) in Hpos.
      rewrite Hfuel in Hpos. cbn in Hpos. lia.
  - destruct (Z.eq_dec (n mod start) 0) as [Hdiv|Hnd].
    + destruct (Z.eq_dec start n) as [->|Hneq].
      * right. intros d Hd. lia.
      * left. exists start. split; [lia|]. apply Z.mod_divide; lia.
    + assert (Hfuel' : Z.to_nat (n - (start + 1)) = fuel).
      { apply Nat2Z.inj.
        rewrite Z2Nat.id by lia.
        assert (Hid : Z.of_nat (Z.to_nat (n - start)) = n - start).
        { apply Z2Nat.id. lia. }
        rewrite Hfuel in Hid. lia. }
      destruct (IH n (start + 1) Hfuel') as [[d Hd]|Hnone]; [lia| lia| |].
      * left. exists d. destruct Hd as [Hrange Hdvd]. split; [lia| exact Hdvd].
      * right. intros d Hd Hdvd.
        assert (d = start \/ start + 1 <= d) by lia.
        destruct H as [->|Hge].
        -- apply Hnd. apply (proj2 (Z.mod_divide n start ltac:(lia))). exact Hdvd.
        -- apply (Hnone d); [lia| exact Hdvd].
Qed.

Lemma factor_search (n start : Z) :
  1 < n -> 1 < start <= n ->
  {d | start <= d < n /\ (d | n)} +
  {forall d, start <= d < n -> ~ (d | n)}.
Proof.
  intros. eapply factor_search_fuel; eauto.
Qed.

Lemma prime_or_factor (n : Z) :
  1 < n ->
  {d | 1 < d < n /\ (d | n)} + {Z.prime n}.
Proof.
  intros Hn.
  destruct (factor_search n 2 Hn ltac:(lia)) as [[d Hd]|Hnone].
  - left. exists d. destruct Hd as [Hrange Hdiv]. split; [lia| exact Hdiv].
  - right. split; [exact Hn|]. intros d Hd Hdiv. apply (Hnone d); [lia| exact Hdiv].
Qed.

Lemma small_prime_factor :
  forall n, 1 < n -> ~ Z.prime n ->
  exists p, Z.prime p /\ (p | n) /\ p * p <= n.
Proof.
  apply (well_founded_induction (Z.lt_wf 0)
    (fun n => 1 < n -> ~ Z.prime n ->
       exists p, Z.prime p /\ (p | n) /\ p * p <= n)).
  intros n IH Hn Hnp.
  destruct (prime_or_factor n Hn) as [[d [Hd Hdiv]]|Hp]; [|contradiction].
  set (k := Z.min d (n / d)).
  destruct (smaller_factor n d k eq_refl Hd Hdiv) as [Hk_range [Hk_sq Hk_div]].
  destruct (prime_or_factor k ltac:(lia)) as [[d' [Hd' Hdiv']]|Hkprime].
  - assert (~ Z.prime k).
    { intros Hkpr. apply (proj2 Hkpr d'); auto. }
    destruct (IH k ltac:(lia) ltac:(lia) H) as [p [Hp [Hpdiv Hpsq]]].
    exists p. split; [exact Hp|]. split.
    + eapply Z.divide_trans; eauto.
    + lia.
  - exists k. split; [exact Hkprime|]. split; [exact Hk_div| exact Hk_sq].
Qed.

Lemma large_factors_prime (n F : Z) :
  1 < n -> 0 < F -> n <= F * F ->
  (forall r, Z.prime r -> (r | n) -> (F | r - 1)) ->
  Z.prime n.
Proof.
  intros Hn HF Hbig Hall.
  destruct (prime_or_factor n Hn) as [[d [Hd Hdiv]]|Hp]; [|exact Hp].
  exfalso.
  assert (Hnp : ~ Z.prime n).
  { intros Hp. apply (proj2 Hp d); auto. }
  destruct (small_prime_factor n Hn Hnp) as [r [Hr [Hrdiv Hrsq]]].
  pose proof (Z.prime_ge_2 r Hr) as Hr2.
  assert (F <= r - 1) by (apply Z.divide_pos_le; auto; lia).
  assert ((F + 1) * (F + 1) <= r * r) by (apply Z.mul_le_mono_nonneg; lia).
  assert ((F + 1) * (F + 1) = F * F + 2 * F + 1) by ring.
  lia.
Qed.

(* If [x ≡ 1 (mod n)] and [r] divides [n], with [r >= 2], then [x ≡ 1 (mod r)]. *)
Lemma mod_one_of_divisor (x n r : Z) :
  2 <= r -> 0 < n -> (r | n) -> x mod n = 1 -> x mod r = 1.
Proof.
  intros Hr Hn Hdiv Hx.
  set (qx := x / n).
  set (qn := n / r).
  assert (Hx' : x = n * qx + 1).
  { unfold qx. rewrite (Z.div_mod x n) at 1 by lia. rewrite Hx. ring. }
  assert (Hn' : n = r * qn).
  { unfold qn. apply div_exact_quotient; [lia| exact Hdiv]. }
  symmetry. apply Z.mod_unique_pos with (q := qn * qx).
  - lia.
  - rewrite Hx', Hn', Z.mul_assoc. reflexivity.
Qed.

Lemma mod_mod_divisor (a n r : Z) :
  0 < r -> 0 < n -> (r | n) -> a mod r = (a mod n) mod r.
Proof.
  intros Hr Hn Hdiv.
  remember (a / n) as qa eqn:Hqa.
  remember (a mod n) as am eqn:Ham.
  remember (n / r) as qn eqn:Hqn.
  assert (Ha : a = n * qa + am).
  { rewrite Hqa, Ham. rewrite (Z.div_mod a n) at 1 by lia. reflexivity. }
  assert (Hn' : n = r * qn).
  { rewrite Hqn. apply div_exact_quotient; [lia| exact Hdiv]. }
  rewrite Ha, Hn', <- Z.mul_assoc.
  replace (r * (qn * qa)) with ((qn * qa) * r) by apply Z.mul_comm.
  rewrite Z.add_comm.
  rewrite (Z.mod_add am (qn * qa) r) by lia.
  reflexivity.
Qed.

Lemma pow_one_modulo (n r a e : Z) :
  2 <= r -> (r | n) -> 0 < n -> 0 <= e ->
  Zmod.pow (Zmod.of_Z n a) e = Zmod.one ->
  Zmod.pow (Zmod.of_Z r a) e = Zmod.one.
Proof.
  intros Hr Hdiv Hn He Hpow.
  assert (Hn2 : 2 <= n).
  { apply Z.le_trans with r; [exact Hr|]. apply Z.divide_pos_le; auto. }
  apply Zmod.to_Z_inj.
  rewrite Zmod.to_Z_pow_nonneg_r by exact He.
  rewrite Zmod.to_Z_of_Z, Zmod.to_Z_1_pos by lia.
  assert (((a mod n) ^ e) mod n = 1).
  { pose proof (f_equal Zmod.to_Z Hpow) as Hto.
    rewrite Zmod.to_Z_pow_nonneg_r in Hto by exact He.
    rewrite Zmod.to_Z_of_Z, Zmod.to_Z_1_pos in Hto by lia.
    exact Hto. }
  assert (Hr0 : 0 < r) by lia.
  rewrite (mod_mod_divisor a n r Hr0 Hn Hdiv).
  rewrite Z.mod_pow_l.
  apply mod_one_of_divisor with (n := n); auto.
Qed.

Lemma gcd_prevents_one (n r a e : Z) :
  Z.prime r -> (r | n) -> 0 <= e -> 2 <= n ->
  Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) e) - 1) n = 1 ->
  Zmod.pow (Zmod.of_Z r a) e <> Zmod.one.
Proof.
  intros Hr Hdiv He Hn Hgcd Heq.
  pose proof (Z.prime_ge_2 r Hr) as Hr2.
  assert (Hone : Zmod.to_Z (Zmod.pow (Zmod.of_Z r a) e) = 1).
  { rewrite Heq. apply Zmod.to_Z_1_pos. lia. }
  rewrite Zmod.to_Z_pow_nonneg_r, Zmod.to_Z_of_Z in Hone by lia.
  assert (Ha1 : a ^ e mod r = 1) by (rewrite <- Z.mod_pow_l; exact Hone).
  set (w := Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) e)).
  assert (Hw : w = (a mod n) ^ e mod n).
  { unfold w. rewrite Zmod.to_Z_pow_nonneg_r, Zmod.to_Z_of_Z by lia. reflexivity. }
  assert (Hr0 : 0 < r) by lia.
  assert (Hn0 : 0 < n) by lia.
  assert (Hw1 : w mod r = 1).
  { rewrite Hw. rewrite <- (mod_mod_divisor ((a mod n) ^ e) n r Hr0 Hn0 Hdiv).
    rewrite <- Z.mod_pow_l. rewrite <- (mod_mod_divisor a n r Hr0 Hn0 Hdiv).
    rewrite Z.mod_pow_l. exact Ha1. }
  assert (Hrd : (r | w - 1)).
  { exists (w / r).
    rewrite (Z.mul_comm (w / r) r).
    rewrite (Z.div_mod w r) at 1 by lia.
    rewrite Hw1. ring. }
  assert ((r | 1)).
  { rewrite <- Hgcd. apply Z.gcd_greatest; auto. }
  apply Z.divide_1_r in H. lia.
Qed.

Lemma pow_bezout_gcd [r : Z] (Hr : Z.prime r) (x : Zmod r)
  (Hx : x <> Zmod.zero) (e : Z)
  (He : Zmod.pow x e = Zmod.one) :
  Zmod.pow x (Z.gcd e (r - 1)) = Zmod.one.
Proof.
  assert (Hcop : Z.gcd (Zmod.to_Z x) r = 1).
  { rewrite Z.gcd_comm. apply Z.coprime_prime_small; auto.
    pose proof (Z.prime_ge_2 r Hr) as Hr2.
    assert (0 <= Zmod.to_Z x < r) by (apply Zmod.to_Z_pos_bound; lia).
    assert (Zmod.to_Z x <> 0) by (apply Zmod.to_Z_nz; exact Hx).
    lia. }
  assert (Hfermat : Zmod.pow x (r - 1) = Zmod.one).
  { replace (r - 1) with (Z.pred r) by lia. apply Zmod.fermat_nz; auto. }
  destruct (Z.extgcd e (r - 1)) as [[u v] g] eqn:Eext.
  destruct (Z.extgcd_correct e (r - 1) Eext) as [Hbez Hg].
  rewrite <- Hg, <- Hbez.
  replace (u * e + v * (r - 1)) with (e * u + (r - 1) * v)
    by (rewrite (Z.mul_comm u e), (Z.mul_comm v (r - 1)); reflexivity).
  rewrite Zmod.pow_add_r_coprime by exact Hcop.
  rewrite !Zmod.pow_mul_r_coprime by exact Hcop.
  rewrite He, Hfermat, !Zmod.pow_1_l.
  rewrite Zmod.mul_1_l. reflexivity.
Qed.

Lemma gcd_div_without_prime (m s q : Z) :
  Z.prime q -> 0 < m -> (q | m) -> ~ (q | s) ->
  (Z.gcd m s | m / q).
Proof.
  intros Hq Hm Hdiv Hnd.
  set (g := Z.gcd m s).
  assert (Hg_m : (g | m)) by apply Z.gcd_divide_l.
  assert (Hcop : Z.gcd g q = 1).
  { rewrite Z.gcd_comm. apply Z.coprime_prime_l; auto.
    intros Hqg. apply Hnd. eapply Z.divide_trans; eauto. apply Z.gcd_divide_r. }
  assert (Hm' : m = q * (m / q)).
  { apply div_exact_quotient; [pose proof (Z.prime_ge_2 q Hq); lia| exact Hdiv]. }
  apply (Z.gauss g q (m / q)).
  - rewrite <- Hm'. exact Hg_m.
  - exact Hcop.
Qed.

Lemma witness_prime_divides_pred (n a q r : Z) :
  Z.prime r -> (r | n) -> 2 <= n -> Z.prime q -> (q | n - 1) ->
  Zmod.pow (Zmod.of_Z n a) (n - 1) = Zmod.one ->
  Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / q)) - 1) n = 1 ->
  (q | r - 1).
Proof.
  intros Hr Hdiv Hn Hq Hqn Hpow Hgcd.
  pose proof (Z.prime_ge_2 r Hr) as Hr2.
  pose proof (Z.prime_ge_2 q Hq) as Hq2.
  set (x := Zmod.of_Z r a).
  assert (Hx : Zmod.pow x (n - 1) = Zmod.one).
  { apply (pow_one_modulo n r a (n - 1)); try exact Hr2; try exact Hdiv;
      try exact Hpow; lia. }
  assert (Hx0 : x <> Zmod.zero).
  { intros Hz.
    assert (Hzp : Zmod.pow x (n - 1) = Zmod.zero).
    { rewrite Hz. apply Zmod.pow_0_l. lia. }
    rewrite Hx in Hzp. exfalso.
    apply (Zmod.one_neq_zero (m := r) ltac:(lia)). exact Hzp. }
  assert (Hgpow : Zmod.pow x (Z.gcd (n - 1) (r - 1)) = Zmod.one).
  { apply pow_bezout_gcd; auto. }
  destruct (Z.eq_dec ((r - 1) mod q) 0) as [Hyes|Hno].
  - apply Z.mod_divide; [lia| exact Hyes].
  - exfalso.
    assert (Hnd : ~ (q | r - 1)).
    { intros Hd. apply Hno. apply (proj2 (Z.mod_divide (r - 1) q ltac:(lia))). exact Hd. }
    set (g := Z.gcd (n - 1) (r - 1)).
    assert (0 < g).
    { pose proof (Z.gcd_nonneg (n - 1) (r - 1)) as Hnn.
      destruct (Z.eq_dec g 0) as [Hz|Hnz].
      - assert (n - 1 = 0).
        { apply Z.divide_0_l. unfold g in Hz. rewrite <- Hz. apply Z.gcd_divide_l. }
        lia.
      - lia. }
    assert (Hgdiv : (g | (n - 1) / q)).
    { apply gcd_div_without_prime; auto; lia. }
    assert (0 <= (n - 1) / q) by (apply Z.div_pos; lia).
    assert (0 <= ((n - 1) / q) / g) by (apply Z.div_pos; lia).
    assert (Hquot : (n - 1) / q = g * (((n - 1) / q) / g)).
    { apply div_exact_quotient; [lia| exact Hgdiv]. }
    assert (Hpowq : Zmod.pow x ((n - 1) / q) = Zmod.one).
    { rewrite Hquot.
      rewrite (Zmod.pow_mul_r_nonneg x g (((n - 1) / q) / g) ltac:(lia) ltac:(lia)).
      unfold g. rewrite Hgpow. apply Zmod.pow_1_l. }
    apply (gcd_prevents_one n r a ((n - 1) / q) Hr Hdiv); auto.
Qed.

Lemma product_of_two_primes (q1 q2 m : Z) :
  Z.prime q1 -> Z.prime q2 -> q1 <> q2 ->
  (q1 | m) -> (q2 | m) -> (q1 * q2 | m).
Proof.
  intros Hq1 Hq2 Hneq H1 H2.
  pose proof (Z.prime_ge_2 q1 Hq1) as Hq1'.
  pose proof (Z.prime_ge_2 q2 Hq2) as Hq2'.
  assert (Hm1 : m = q1 * (m / q1)).
  { apply div_exact_quotient; [lia| exact H1]. }
  assert (H2' : (q2 | m / q1)).
  { apply (Z.gauss q2 q1 (m / q1)).
    - rewrite <- Hm1. exact H2.
    - rewrite Z.gcd_comm. apply Z.coprime_prime_l; auto.
      intros Hdiv. apply Hneq. apply Z.divide_prime_prime; auto. }
  assert (Hm2 : m / q1 = q2 * ((m / q1) / q2)).
  { apply div_exact_quotient; [lia| exact H2']. }
  set (k := (m / q1) / q2).
  exists k.
  rewrite Hm1, Hm2. fold k.
  rewrite (Z.mul_assoc q1 q2 k).
  apply Z.mul_comm.
Qed.

Theorem pocklington1 (n F a : Z)
  (Hpow : Zmod.eqb (Zmod.pow (Zmod.of_Z n a) (n - 1)) Zmod.one = true)
  (Hgcd : (Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / F)) - 1) n =? 1) = true)
  (H1 : (1 <? n) = true)
  (Hbig : (n <=? F * F) = true)
  (Hdiv : ((n - 1) mod F =? 0) = true)
  (HF : Z.prime F)
  : Z.prime n.
Proof.
  apply Z.ltb_lt in H1. apply Z.leb_le in Hbig. apply Z.eqb_eq in Hdiv.
  assert (Hpow' : Zmod.pow (Zmod.of_Z n a) (n - 1) = Zmod.one)
    by (apply zmod_eqb_true; exact Hpow).
  assert (Hgcd' : Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / F)) - 1) n = 1)
    by (apply Z.eqb_eq; exact Hgcd).
  pose proof (Z.prime_ge_2 F HF) as HF2.
  apply large_factors_prime with (F := F); auto; [lia|].
  intros r Hr Hrn.
  apply (witness_prime_divides_pred n a F r); auto.
  - lia.
  - apply (proj1 (Z.mod_divide (n - 1) F ltac:(lia))). exact Hdiv.
Qed.

Theorem pocklington2 (n q1 q2 a : Z)
  (Hpow : Zmod.eqb (Zmod.pow (Zmod.of_Z n a) (n - 1)) Zmod.one = true)
  (Hg1 : (Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / q1)) - 1) n =? 1) = true)
  (Hg2 : (Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / q2)) - 1) n =? 1) = true)
  (H1 : (1 <? n) = true)
  (Hbig : (n <=? (q1 * q2) * (q1 * q2)) = true)
  (Hdiv : ((n - 1) mod (q1 * q2) =? 0) = true)
  (Hneq : (q1 =? q2) = false)
  (Hq1 : Z.prime q1)
  (Hq2 : Z.prime q2)
  : Z.prime n.
Proof.
  apply Z.ltb_lt in H1. apply Z.leb_le in Hbig. apply Z.eqb_eq in Hdiv.
  apply Z.eqb_neq in Hneq.
  assert (Hpow' : Zmod.pow (Zmod.of_Z n a) (n - 1) = Zmod.one)
    by (apply zmod_eqb_true; exact Hpow).
  assert (Hg1' : Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / q1)) - 1) n = 1)
    by (apply Z.eqb_eq; exact Hg1).
  assert (Hg2' : Z.gcd (Zmod.to_Z (Zmod.pow (Zmod.of_Z n a) ((n - 1) / q2)) - 1) n = 1)
    by (apply Z.eqb_eq; exact Hg2).
  pose proof (Z.prime_ge_2 q1 Hq1) as Hq1'.
  pose proof (Z.prime_ge_2 q2 Hq2) as Hq2'.
  set (F := q1 * q2).
  assert (HF0 : 0 < F) by (unfold F; nia).
  assert (HFdiv : (F | n - 1)).
  { apply (proj1 (Z.mod_divide (n - 1) F ltac:(lia))). exact Hdiv. }
  apply large_factors_prime with (F := F); auto.
  intros r Hr Hrn.
  assert (Hq1d : (q1 | r - 1)).
  { apply (witness_prime_divides_pred n a q1 r); auto.
    - lia.
    - eapply Z.divide_trans; [| exact HFdiv]. unfold F. exists q2. apply Z.mul_comm. }
  assert (Hq2d : (q2 | r - 1)).
  { apply (witness_prime_divides_pred n a q2 r); auto.
    - lia.
    - eapply Z.divide_trans; [| exact HFdiv]. unfold F. exists q1. reflexivity. }
  apply product_of_two_primes; auto.
Qed.

Ltac vmbulk :=
  lazymatch goal with
  | |- (_ = true) => vm_compute; reflexivity
  | |- (_ = false) => vm_compute; reflexivity
  end.
