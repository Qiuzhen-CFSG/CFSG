module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.Transport
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoFixedField

/-!
# The minus-four/PSL₂ comparison over every finite binary coefficient field

A field of order `2^n`, with `n > 0`, is isomorphic to the actual Frobenius
fixed field inside `GF(2^(2n))`. The semilinear quadratic-form comparison in
`Transport` adjusts the independently chosen anisotropic-plane parameters;
it induces an equivalence of the full commutator groups and their literal
scalar quotients. Composing with the existing Hermitian determinant action
therefore gives `PΩ⁻₄(F) ≃ PSL₂(GF(2^(2n)))` with no additional model premises.

This is the arbitrary-field comparison used to remove the rank-one minus
alias in the Lie-family branch of Theorem D. The general model-predicate
adapter and faithful-local-family exclusion belong to its Chapter 14 consumer.
Sources: GLS3 §2.7; Aschbacher–Smith I.1.6(3), printed p.408, A.2.18, printed
p.40, and Theorem D/14.8.2, printed pp.1078–1079 (`refs/quasithin.pdf`).
-/

public noncomputable section

namespace ClassicalOrthogonal.TheoremDRootNormalizer
universe u
open Representation.OrthogonalFourMinus

variable (F : Type u) [Field F] [Finite F]

/-- The genuine rank-two minus orthogonal group over any field of order `2^n`
is PSL₂ over the specified quadratic Galois field, including `n = 1`. -/
def minusTwoEquivPSL {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = 2 ^ n) :
    ClassicalGroup.POmegaMinus 2 F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * n)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (FiniteModel.fixedField n) := Fintype.ofFinite _
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [← Nat.card_eq_fintype_card] using hcard)
  let σ : F ≃+* FiniteModel.fixedField n := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans (FiniteModel.card_fixedField n).symm)
  exact (MinusTwoComparison.minusProjectiveFieldEquiv σ 2).trans (minusTwoFixedFieldEquivPSL n)

/-- The arbitrary-field minus-four/PSL₂ comparison as an existence statement. -/
theorem nonempty_minusTwoEquivPSL {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = 2 ^ n) :
    Nonempty (ClassicalGroup.POmegaMinus 2 F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * n))) :=
  ⟨minusTwoEquivPSL F hn hcard⟩

end ClassicalOrthogonal.TheoremDRootNormalizer
