# Pasta curves in Rocq

Primality, ellipticity, and the 2-adic structure of the Pasta curves (Pallas and Vesta), checked in Rocq 9.3 against the standard library only. The statements follow the Lean 4 development [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

Both curves are the short Weierstrass curve `y² = x³ + 5`.

- `pallas_p` is the Pallas base field and the Vesta scalar field.
- `vesta_p` is the Vesta base field and the Pallas scalar field.

## What is proved

- `pallas_p` and `vesta_p` are prime, by Pocklington's criterion. A square-free divisor `F` of `n - 1` with `F² ≥ n`, a witness `a^(n-1) ≡ 1 (mod n)`, and `gcd(a^((n-1)/q) - 1, n) = 1` for each prime `q` dividing `F`, imply that `n` is prime. The leaves of the certificate tree are trial division; each step above that is a few `vm_compute` goals.
- The factorizations `p - 1 = 2^32 · 3 · 463 · A · B` and `q - 1 = 2^32 · 3² · 1709 · 24859 · C · D`, with every factor prime, and with the cofactor of `2^32` odd. The 2-adic valuation is exactly 32.
- Hex, decimal, and `2^254 + offset` forms of both moduli, and the bounds `2^254 < p, q < 2^255`.
- The discriminant of `y² = x³ + 5` is `-10800`, and it is a unit in both fields, so both curves are elliptic.
- `Zmod pallas_p` and `Zmod vesta_p` are fields.
- The point `(-1, 2)` lies on the curve over every `Zmod m`. It is the integer identity `2² = (-1)³ + 5`.

## What is not proved

The 2-cycle is not proved. `|Pallas(F_p)| = q` and `|Vesta(F_q)| = p` need a point count (Schoof), which the standard library does not provide. `cycle_conjecture_pallas` and `cycle_conjecture_vesta` state it for the affine points: a duplicate-free list of solutions of `y² = x³ + 5` whose length is the other prime minus one. The point at infinity makes up the group order. Both are defined as propositions, not axioms, so the development has no axioms; a result that depends on the cycle has to take them as hypotheses.

The elliptic-curve group law is not formalized. Associativity is the long part, and nothing here depends on it.

## Build

```sh
make
```

`Certificates.v` runs the modular exponentiations for the two 255-bit primes. A full build takes a few seconds. `make clean` deletes the compiled files.
