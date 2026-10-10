(* Prints the assumptions of the headline theorems.  [make check] fails if any
   of these lines reports an axiom. *)

From Pasta Require Import Trial Pocklington Certificates Curve.

Print Assumptions primeb_prime.
Print Assumptions pocklington1.
Print Assumptions pocklington2.
Print Assumptions pallas_p_prime.
Print Assumptions vesta_p_prime.
Print Assumptions pallas_is_field.
Print Assumptions vesta_is_field.
Print Assumptions pallas_nonsingular.
Print Assumptions vesta_nonsingular.
Print Assumptions pallas_discriminant_unit.
Print Assumptions vesta_discriminant_unit.
Print Assumptions pallas_two_adicity.
Print Assumptions vesta_two_adicity.
Print Assumptions pallas_omega_primitive.
Print Assumptions vesta_omega_primitive.
Print Assumptions generator_on_curve.
Print Assumptions pallas_generator_mul_order.
Print Assumptions vesta_generator_mul_order.
