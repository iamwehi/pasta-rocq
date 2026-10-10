(* The Pasta curves: Pallas is [y^2 = x^3 + 5] over [Zmod pallas_p], and Vesta
   is the same equation over [Zmod vesta_p].

   Proved here: both moduli are prime (via [Certificates]), both fields are
   fields, neither curve has a singular point, the shared discriminant
   [-10800] is a unit, the point [(-1, 2)]
   lies on the curve, and [p - 1] and [q - 1] have 2-adic valuation exactly
   32.

   Not proved: the elliptic-curve group law, and the 2-cycle
   [|Pallas(F_p)| = q], [|Vesta(F_q)| = p].  Point counting (Schoof) is not
   in the standard library, so the cycle is stated as two propositions and
   left unproved, in the same way the Lean development leaves it as a
   conjecture.  Affine points only: the point at infinity accounts for the
   final [+ 1]. *)

From Stdlib Require Import ZArith Zmod Lia List Field_theory.
From Pasta Require Import Certificates.
Local Open Scope Z_scope.

(** Decimal and [2^254] forms of the hex literals in [Certificates]. *)

Theorem pallas_p_decimal :
  pallas_p = 28948022309329048855892746252171976963363056481941560715954676764349967630337.
Proof. reflexivity. Qed.

Theorem vesta_p_decimal :
  vesta_p = 28948022309329048855892746252171976963363056481941647379679742748393362948097.
Proof. reflexivity. Qed.

Theorem pallas_p_pow254 :
  pallas_p = 2 ^ 254 + 45560315531419706090280762371685220353.
Proof. vm_compute. reflexivity. Qed.

Theorem vesta_p_pow254 :
  vesta_p = 2 ^ 254 + 45560315531506369815346746415080538113.
Proof. vm_compute. reflexivity. Qed.

Theorem vesta_minus_pallas :
  vesta_p - pallas_p = 86663725065984043395317760.
Proof. vm_compute. reflexivity. Qed.

Theorem pallas_p_bounds : 2 ^ 254 < pallas_p < 2 ^ 255.
Proof. split; apply Z.ltb_lt; vm_compute; reflexivity. Qed.

Theorem vesta_p_bounds : 2 ^ 254 < vesta_p < 2 ^ 255.
Proof. split; apply Z.ltb_lt; vm_compute; reflexivity. Qed.

(** [p - 1 = 2^32 * 3 * 463 * A * B] and [q - 1 = 2^32 * 3^2 * 1709 * 24859 * C * D]. *)

Theorem pallas_p_factorization :
  pallas_p - 1 = 2 ^ 32 * 3 * 463 * pallas_A * pallas_B.
Proof. vm_compute. reflexivity. Qed.

Theorem vesta_p_factorization :
  vesta_p - 1 = 2 ^ 32 * 3 ^ 2 * 1709 * 24859 * vesta_C * vesta_D.
Proof. vm_compute. reflexivity. Qed.

Theorem pallas_factors_prime :
  Z.prime 2 /\ Z.prime 3 /\ Z.prime 463 /\ Z.prime pallas_A /\ Z.prime pallas_B.
Proof.
  exact (conj Z.prime_2 (conj Z.prime_3 (conj prime_463 (conj pallas_A_prime pallas_B_prime)))).
Qed.

Theorem vesta_factors_prime :
  Z.prime 2 /\ Z.prime 3 /\ Z.prime 1709 /\ Z.prime 24859 /\
  Z.prime vesta_C /\ Z.prime vesta_D.
Proof.
  exact (conj Z.prime_2 (conj Z.prime_3 (conj prime_1709
    (conj prime_24859 (conj vesta_C_prime vesta_D_prime))))).
Qed.

(** Exact 2-valuation 32: the cofactor of [2^32] is odd, so these moduli
    support an NTT of depth 32 and no more. *)

Theorem pallas_two_adicity :
  exists t, pallas_p - 1 = 2 ^ 32 * t /\ t mod 2 = 1.
Proof.
  exists ((pallas_p - 1) / 2 ^ 32). split.
  - apply (proj2 (Z.div_exact (pallas_p - 1) (2 ^ 32) ltac:(lia))).
    vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Theorem vesta_two_adicity :
  exists t, vesta_p - 1 = 2 ^ 32 * t /\ t mod 2 = 1.
Proof.
  exists ((vesta_p - 1) / 2 ^ 32). split.
  - apply (proj2 (Z.div_exact (vesta_p - 1) (2 ^ 32) ltac:(lia))).
    vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** Shared short Weierstrass equation [y^2 = x^3 + 5], discriminant
    [-16 * (4*0^3 + 27*5^2) = -10800]. *)

Definition curve_b : Z := 5.
Definition curve_discriminant : Z := -10800.

Theorem curve_discriminant_value :
  curve_discriminant = -16 * (4 * 0 ^ 3 + 27 * curve_b ^ 2).
Proof. reflexivity. Qed.

Definition on_curve (m : Z) (pt : Zmod m * Zmod m) : Prop :=
  let (x, y) := pt in
  Zmod.pow y 2 = Zmod.add (Zmod.pow x 3) (Zmod.of_Z m curve_b).

Lemma discriminant_nonzero (m : Z) :
  10800 < m -> Zmod.of_Z m curve_discriminant <> Zmod.zero.
Proof.
  intro Hm. apply Zmod.of_Z_nz.
  assert (curve_discriminant mod m = m - 10800).
  { unfold curve_discriminant.
    replace (-10800) with ((m - 10800) + (-1) * m) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite H. lia.
Qed.

Theorem discriminant_unit (m : Z) :
  Z.prime m -> 10800 < m ->
  Zmod.mul (Zmod.inv (Zmod.of_Z m curve_discriminant))
    (Zmod.of_Z m curve_discriminant) = Zmod.one.
Proof.
  intros Hp Hm. apply Zmod.mul_inv_same_l_prime; [exact Hp|].
  apply discriminant_nonzero. exact Hm.
Qed.

Theorem pallas_discriminant_unit :
  Zmod.mul (Zmod.inv (Zmod.of_Z pallas_p curve_discriminant))
    (Zmod.of_Z pallas_p curve_discriminant) = Zmod.one.
Proof.
  apply discriminant_unit; [exact pallas_p_prime|].
  apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Theorem vesta_discriminant_unit :
  Zmod.mul (Zmod.inv (Zmod.of_Z vesta_p curve_discriminant))
    (Zmod.of_Z vesta_p curve_discriminant) = Zmod.one.
Proof.
  apply discriminant_unit; [exact vesta_p_prime|].
  apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

(** Nonsingularity, stated directly rather than through the discriminant.
    With [F(x, y) = y^2 - x^3 - 5], a singular point is a solution of
    [F = 0] at which both partials [-3x^2] and [2y] vanish. *)

Definition singular_point (m : Z) (pt : Zmod m * Zmod m) : Prop :=
  let (x, y) := pt in
  on_curve m pt /\
  Zmod.opp (Zmod.mul (Zmod.of_Z m 3) (Zmod.pow x 2)) = Zmod.zero /\
  Zmod.mul (Zmod.of_Z m 2) y = Zmod.zero.

Theorem curve_nonsingular (m : Z) :
  Z.prime m -> 5 < m -> forall pt, ~ singular_point m pt.
Proof.
  intros Hp Hm [x y] (Hon & Hx & Hy).
  unfold on_curve, curve_b in Hon.
  assert (H2 : Zmod.of_Z m 2 <> Zmod.zero).
  { apply Zmod.of_Z_nz. rewrite Z.mod_small by lia. lia. }
  assert (H3 : Zmod.of_Z m 3 <> Zmod.zero).
  { apply Zmod.of_Z_nz. rewrite Z.mod_small by lia. lia. }
  assert (H5 : Zmod.of_Z m 5 <> Zmod.zero).
  { apply Zmod.of_Z_nz. rewrite Z.mod_small by lia. lia. }
  apply (proj1 (Zmod.mul_0_iff_prime Hp _ _)) in Hy.
  destruct Hy as [|Hy]; [contradiction|]. subst y.
  apply (f_equal Zmod.opp) in Hx. rewrite Zmod.opp_opp, Zmod.opp_0 in Hx.
  apply (proj1 (Zmod.mul_0_iff_prime Hp _ _)) in Hx.
  destruct Hx as [|Hx]; [contradiction|].
  rewrite Zmod.pow_2_r in Hx.
  apply (proj1 (Zmod.mul_0_iff_prime Hp _ _)) in Hx.
  destruct Hx as [Hx|Hx]; subst x;
    rewrite !Zmod.pow_0_l, Zmod.add_0_l in Hon by lia;
    apply H5; symmetry; exact Hon.
Qed.

Theorem pallas_nonsingular : forall pt, ~ singular_point pallas_p pt.
Proof.
  apply curve_nonsingular; [exact pallas_p_prime|].
  apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Theorem vesta_nonsingular : forall pt, ~ singular_point vesta_p pt.
Proof.
  apply curve_nonsingular; [exact vesta_p_prime|].
  apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Theorem pallas_is_field :
  @field_theory (Zmod pallas_p) Zmod.zero Zmod.one Zmod.add Zmod.mul
    Zmod.sub Zmod.opp Zmod.mdiv Zmod.inv eq.
Proof. apply Zmod.field_theory. exact pallas_p_prime. Qed.

Theorem vesta_is_field :
  @field_theory (Zmod vesta_p) Zmod.zero Zmod.one Zmod.add Zmod.mul
    Zmod.sub Zmod.opp Zmod.mdiv Zmod.inv eq.
Proof. apply Zmod.field_theory. exact vesta_p_prime. Qed.

(** The protocol generator [(-1, 2)].  This is the integer identity
    [2^2 = (-1)^3 + 5], transported along [Zmod.of_Z]. *)

Definition generator (m : Z) : Zmod m * Zmod m :=
  (Zmod.of_Z m (-1), Zmod.of_Z m 2).

Theorem generator_on_curve (m : Z) : on_curve m (generator m).
Proof.
  unfold on_curve, generator.
  rewrite <- (Zmod.of_Z_pow 2 2 ltac:(lia)).
  rewrite <- (Zmod.of_Z_pow (-1) 3 ltac:(lia)).
  rewrite <- Zmod.of_Z_add.
  replace ((-1) ^ 3 + 5) with (2 ^ 2) by reflexivity.
  reflexivity.
Qed.

(** The 2-cycle.  [pts] enumerates the affine points, so its length is one
    less than the group order.  These are statements, not assumptions:
    anything that needs the cycle must take them as hypotheses. *)

Definition cycle_conjecture_pallas : Prop :=
  exists pts : list (Zmod pallas_p * Zmod pallas_p),
    NoDup pts /\
    Z.of_nat (length pts) = vesta_p - 1 /\
    (forall pt, In pt pts <-> on_curve pallas_p pt).

Definition cycle_conjecture_vesta : Prop :=
  exists pts : list (Zmod vesta_p * Zmod vesta_p),
    NoDup pts /\
    Z.of_nat (length pts) = pallas_p - 1 /\
    (forall pt, In pt pts <-> on_curve vesta_p pt).
