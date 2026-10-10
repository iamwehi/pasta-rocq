(* Primality of the Pasta field primes and of every prime that appears in
   their Pocklington certificates.

   Leaves whose square root is tiny are discharged by [primeb].  Everything
   larger is one application of [pocklington1] or [pocklington2]; each of
   those is a few [vm_compute] goals (a modular exponentiation and a gcd). *)

From Stdlib Require Import ZArith Zmod.
From Pasta Require Import Trial Pocklington.
Local Open Scope Z_scope.

Ltac trial := apply primeb_prime; vm_compute; reflexivity.

Lemma prime_19 : Z.prime 19. Proof. trial. Qed.
Lemma prime_463 : Z.prime 463. Proof. trial. Qed.
Lemma prime_977 : Z.prime 977. Proof. trial. Qed.
Lemma prime_1709 : Z.prime 1709. Proof. trial. Qed.
Lemma prime_2557 : Z.prime 2557. Proof. trial. Qed.
Lemma prime_3767 : Z.prime 3767. Proof. trial. Qed.
Lemma prime_6091 : Z.prime 6091. Proof. trial. Qed.
Lemma prime_12149 : Z.prime 12149. Proof. trial. Qed.
Lemma prime_24859 : Z.prime 24859. Proof. trial. Qed.
Lemma prime_31649 : Z.prime 31649. Proof. trial. Qed.
Lemma prime_125803 : Z.prime 125803. Proof. trial. Qed.
Lemma prime_413527 : Z.prime 413527. Proof. trial. Qed.
Lemma prime_772231 : Z.prime 772231. Proof. trial. Qed.
Lemma prime_897019 : Z.prime 897019. Proof. trial. Qed.
Lemma prime_958679 : Z.prime 958679. Proof. trial. Qed.

Lemma prime_2012849 : Z.prime 2012849.
Proof. apply (pocklington1 2012849 125803 3); try vmbulk. exact prime_125803. Qed.

Lemma prime_4025699 : Z.prime 4025699.
Proof. apply (pocklington1 4025699 2012849 2); try vmbulk. exact prime_2012849. Qed.

Lemma prime_5701177 : Z.prime 5701177.
Proof. apply (pocklington1 5701177 6091 7); try vmbulk. exact prime_6091. Qed.

Lemma prime_6942563 : Z.prime 6942563.
Proof.
  apply (pocklington2 6942563 977 19 2); try vmbulk.
  - exact prime_977.
  - exact prime_19.
Qed.

Lemma prime_1197907 : Z.prime 1197907.
Proof. apply (pocklington1 1197907 3767 3); try vmbulk. exact prime_3767. Qed.

Lemma prime_4229279 : Z.prime 4229279.
Proof. apply (pocklington1 4229279 2557 13); try vmbulk. exact prime_2557. Qed.

Lemma prime_80513981 : Z.prime 80513981.
Proof. apply (pocklington1 80513981 4025699 2); try vmbulk. exact prime_4025699. Qed.

Lemma prime_41655379 : Z.prime 41655379.
Proof. apply (pocklington1 41655379 6942563 3); try vmbulk. exact prime_6942563. Qed.

Lemma prime_399082391 : Z.prime 399082391.
Proof. apply (pocklington1 399082391 5701177 7); try vmbulk. exact prime_5701177. Qed.

Lemma prime_417677162933 : Z.prime 417677162933.
Proof. apply (pocklington1 417677162933 897019 2); try vmbulk. exact prime_897019. Qed.

Lemma prime_22160661629 : Z.prime 22160661629.
Proof. apply (pocklington1 22160661629 41655379 3); try vmbulk. exact prime_41655379. Qed.

Lemma prime_325086459374267 : Z.prime 325086459374267.
Proof.
  apply (pocklington2 325086459374267 772231 413527 2); try vmbulk.
  - exact prime_772231.
  - exact prime_413527.
Qed.

Lemma prime_4129989133 : Z.prime 4129989133.
Proof. apply (pocklington1 4129989133 958679 5); try vmbulk. exact prime_958679. Qed.

Lemma prime_5247740253619 : Z.prime 5247740253619.
Proof. apply (pocklington1 5247740253619 80513981 2); try vmbulk. exact prime_80513981. Qed.

Lemma prime_5239247429827 : Z.prime 5239247429827.
Proof.
  apply (pocklington2 5239247429827 31649 12149 2); try vmbulk.
  - exact prime_31649.
  - exact prime_12149.
Qed.

(* Odd prime factors of [pallas_p - 1] and [vesta_p - 1].  The cofactor of
   [F] in Pocklington's criterion is what keeps the powers of 2 and 3 out
   of [F]; those are recovered in [Curve.v]. *)
Definition pallas_A : Z := 539204044132271846773.
Definition pallas_B : Z := 8999194758858563409123804352480028797519453.
Definition vesta_C : Z := 1690502597179744445941507.
Definition vesta_D : Z := 10427374428728808478656897599072717.

Lemma pallas_A_prime : Z.prime pallas_A.
Proof. apply (pocklington1 pallas_A 417677162933 5); try vmbulk. exact prime_417677162933. Qed.

Lemma pallas_B_prime : Z.prime pallas_B.
Proof.
  apply (pocklington2 pallas_B 325086459374267 22160661629 2); try vmbulk.
  - exact prime_325086459374267.
  - exact prime_22160661629.
Qed.

Lemma vesta_C_prime : Z.prime vesta_C.
Proof. apply (pocklington1 vesta_C 5247740253619 2); try vmbulk. exact prime_5247740253619. Qed.

Lemma vesta_D_prime : Z.prime vesta_D.
Proof.
  apply (pocklington2 vesta_D 5239247429827 399082391 2); try vmbulk.
  - exact prime_5239247429827.
  - exact prime_399082391.
Qed.

(* Pallas base field and Vesta scalar field. *)
Definition pallas_p : Z :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001.
(* Vesta base field and Pallas scalar field. *)
Definition vesta_p : Z :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001.

Theorem pallas_p_prime : Z.prime pallas_p.
Proof. apply (pocklington1 pallas_p pallas_B 5); try vmbulk. exact pallas_B_prime. Qed.

Theorem vesta_p_prime : Z.prime vesta_p.
Proof.
  apply (pocklington2 vesta_p vesta_D vesta_C 5); try vmbulk.
  - exact vesta_D_prime.
  - exact vesta_C_prime.
Qed.
