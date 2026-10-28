module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PartitionCore

/-!
# Scalar conjugation on the cubic quotients of the two blocks

Conjugation by a permutation of four points acts on A₄/V₄ according to
its sign. The corresponding assertion on A₃ is exact. We express the
first assertion by a square-one discrepancy, avoiding any quotient or
chosen generator. The two finite checks range over 24² and 6² pairs.

These bounded calculations are compiled separately from the source-local
interfaces, so their kernel checks require only the permutation imports.

Source application: Aschbacher–Smith, 13.8.24, printed p.958
(1 March 2004 manuscript).
-/

public section
open Equiv
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.CubicParity

set_option maxRecDepth 10000 in
/-- Conjugation acts by the sign scalar on A₄ modulo its Klein four group,
expressed by the square-one property of the discrepancy. -/
theorem four_scalar_square : ∀ (t c : Perm (Fin 4)), c.sign = 1 →
    (t * c * t⁻¹ * (if t.sign = 1 then c⁻¹ else c)) ^ 2 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Conjugation on the cubic subgroup of S₃ is the sign scalar. -/
theorem three_scalar : ∀ (t c : Perm (Fin 3)), c.sign = 1 →
    t * c * t⁻¹ * (if t.sign = 1 then c⁻¹ else c) = 1 := by
  decide +kernel

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection.CubicParity
