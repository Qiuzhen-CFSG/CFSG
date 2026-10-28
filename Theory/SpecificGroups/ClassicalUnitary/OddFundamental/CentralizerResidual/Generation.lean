module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.SmallGeneration
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.PlaneRotations
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.VectorReduction

/-!
# Defining-prime generation in the actual unitary centralizer

Norm-one-vector reduction and the matrix stabilizer induction prove that the
actual SU₂ images generate the full identity-form SUₙ over the original field.
Each image lies in the prime-to-r residual by the SU₂–SL₂ comparison over the
actual fixed field. Thus SUₙ equals its prime-to-r residual for every positive
dimension, including q = 3.

Applying this generation theorem to the literal complementary embedding gives
the lower inclusion in the marked projective centralizer residual. The reverse
inclusion is the independent covering-centralizer calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.17,
printed pp.38–39 of `refs/quasithin.pdf`, J* ≅ SU_{N-2}(q).
-/

public section
open BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- The geometric reduction supplies the lower residual inclusion on the
original complementary embedding. -/
theorem complement_le_residual_of_unitVectorReduction [Finite F]
    {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) (hn : 0 < n)
    (hred : ∀ k, Generation.UnitVectorReduction σ hσ k) :
    (complementInCentralizer σ hσ (n := n)).range ≤ residual σ hσ r :=
  complement_le_residual_of_generation σ hσ
    (Generation.special_primeToResidual_eq_top_of_reduction σ hσ hr he hc hj hred hn)

/-- The full identity-form SUₙ is its defining-prime residual, including q = 3. -/
theorem special_primeToResidual_eq_top [Finite F]
    {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) (hn : 0 < n) :
    primeToResidual r (form σ hσ n).specialSubgroup = ⊤ := by
  have hh := Generation.twoSpaceGenerated_le_primeToResidual σ hσ hr he hc hj (n := n)
  rw [Generation.twoSpaceGenerated_eq_top σ hσ hr he hc hj hn] at hh
  exact top_unique hh

/-- The original complementary SUₙ image lies in the marked centralizer residual.
This discharges the generation input in the complementary residual calculation. -/
theorem complement_le_residual [Finite F]
    {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) (hn : 0 < n) :
    (complementInCentralizer σ hσ (n := n)).range ≤ residual σ hσ r :=
  complement_le_residual_of_generation σ hσ
    (special_primeToResidual_eq_top σ hσ hr he hc hj hn)

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
