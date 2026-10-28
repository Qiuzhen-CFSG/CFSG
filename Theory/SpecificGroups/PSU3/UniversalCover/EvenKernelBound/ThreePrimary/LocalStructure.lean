module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection

/-!+# The local torus input for the three-primary PSU₃ kernel bound

The intended torus is the image of the norm-one determinant-one diagonal
matrices, with the scalar cube roots still factored out. A coordinate
transposition swaps its two generators; a three-cycle supplies a subgroup
of index prime to three. Its fixed subgroup in the projective torus has
order three. For a binary field the torus has odd order, so these facts
force its full preimage in a central extension to be abelian.

This module records precisely the matrix facts consumed by `ThreePrimary`.
It does not assert their existence. No central-extension or multiplier
conclusion occurs among the fields.

Source: Aschbacher–Smith I.1.3(2), printed p.407 (PDF p.418), and
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary

variable {F : Type*} [Field F] (J : HermitianForm 3 F) (n : ℕ)

/-- Concrete local subgroup data in the actual projective unitary group.
The torus need not be a three-group: prime-to-three index is sufficient
for transfer, and using the entire norm-one torus avoids any restriction
on the valuation of three in `2^n + 1`. -/
structure TorusConfiguration where
  torus : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)
  first : ProjectiveSpecialUnitaryMatrixGroup J
  second : ProjectiveSpecialUnitaryMatrixGroup J
  cycle : ProjectiveSpecialUnitaryMatrixGroup J
  swap : ProjectiveSpecialUnitaryMatrixGroup J
  generate : closure ({first, second} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = torus
  commute : Commute first second
  swap_first : swap * first * swap⁻¹ = second
  swap_second : swap * second * swap⁻¹ = first
  first_pow : first ^ (2 ^ n + 1) = 1
  normalizes : cycle ∈ normalizer (torus : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  index_prime_to_three : ¬ 3 ∣ (torus ⊔ zpowers cycle).index
  fixed_card_le : Nat.card (torus ⊓ centralizer ({cycle} :
    Set (ProjectiveSpecialUnitaryMatrixGroup J)) : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary
