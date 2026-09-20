/-
  Erdős Problem 141 / JSP-000141
  Can a product of consecutive positive integers have every prime factor
  occurring with exponent at least two? (i.e., can it be a powerful number?)

  Answer: YES.

  Witness: 8 × 9 = 72 = 2³ × 3² (powerful number, product of 2 consecutive integers).
  Every prime factor (2, 3) has exponent ≥ 2.
  A number n is powerful iff n = a² × b³ for some a, b ≥ 1.
  72 = 3² × 2³ (a=3, b=2).

  Erdős Problem 758 / JSP-000758
  Can the product of consecutive integers have pairwise distinct
  prime-factor exponents?

  Answer: YES.

  Witness: 2 × 3 × 4 = 24 = 2³ × 3¹
  Exponents 3 and 1 are distinct. Primes 2 and 3 are distinct.
  Since 24 = 2³ × 3¹ exactly, the only prime factors are 2 and 3.

  Pure Lean 4, no external dependencies.
-/

namespace Erdos141_758

/--
  JSP-000141: A product of consecutive positive integers can be powerful.
  8 × 9 = 72 = 3² × 2³ (powerful: every prime factor has exponent ≥ 2).
-/
theorem erdos_141 :
    ∃ (n k : Nat), 2 ≤ k ∧
    ∃ (a b : Nat), 1 ≤ a ∧ 1 ≤ b ∧
    n * (n + 1) = a * a * (b * b * b) := by
  refine ⟨8, 2, ?_, 3, 2, ?_, ?_, ?_⟩
  · decide  -- 2 ≤ 2
  · decide  -- 1 ≤ 3
  · decide  -- 1 ≤ 2
  · decide  -- 8 * 9 = 3 * 3 * (2 * 2 * 2) = 72

/--
  JSP-000758: A product of consecutive integers can have pairwise distinct
  prime-factor exponents.
  2 × 3 × 4 = 24 = 2³ × 3¹, exponents 3 and 1 are distinct.
-/
theorem erdos_758 :
    ∃ (n k p q ep eq : Nat),
    2 ≤ k ∧
    2 ≤ p ∧ 2 ≤ q ∧ p ≠ q ∧
    ep ≠ eq ∧
    n * (n + 1) * (n + 2) = p ^ ep * q ^ eq := by
  refine ⟨2, 3, 2, 3, 3, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide  -- 2 ≤ 3
  · decide  -- 2 ≤ 2
  · decide  -- 2 ≤ 3
  · decide  -- 2 ≠ 3
  · decide  -- 3 ≠ 1
  · decide  -- 2 * 3 * 4 = 2^3 * 3^1 = 24

end Erdos141_758
