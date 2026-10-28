module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.PairModel
public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LiteralPairs
public import Theory.SpecificGroups.Monster.Construction.LocalC.Action

/-!
# The literal matrix pair action

The natural action of `N1` has the signed coordinate transport already
recovered from its Parker halfspaces. The fixed natural-to-Leech comparison
transfers that action to marked coordinate vectors. Polarizing the rank-one
covariance theorem gives the action on the existing off-diagonal pair
matrices, then on their literal inclusion in the Griess carrier.

This supplies the matrix branch of `LocalCompatibility` without choosing
another representation or changing the normalization of the pair vectors.
Source: Aschbacher, *Sporadic Groups*, 27.4 and 29.10(3), pp. 146, 159.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin SignedModules.Natural LocalC Atlas.Codes Atlas.Fischer

private theorem natural_basis_sign (g : N1) (x : Omega) :
    NaturalAction.representation g (basis 0 x) =
      sign (coordinateShift g.val 0 x) • basis 0 (coordinatePermutation g.val x) := by
  rw [basis_eq_L, naturalAction_L]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (coordinateShift g.val 0 x) with h | h
  · simp [h, basis_eq_L]
  · simp only [h, show (1 : ParkerBit) + 1 = 0 from rfl, L_zero, sign_one]
    exact (neg_one_smul ℝ _).symm

private theorem natural_point_sign (g : N1) (x : Omega) :
    realLeechRepresentation (n1LeechRepresentation g) (pointVector x) =
      sign (coordinateShift g.val 0 x) • pointVector (coordinatePermutation g.val x) := by
  rw [show pointVector x = naturalLeechComparison (basis 0 x) from
    (by rw [basis_eq_L, naturalLeechComparison_L_one]; rfl), n1LeechRepresentation_natural,
    natural_basis_sign, map_smul, basis_eq_L, naturalLeechComparison_L_one]
  rfl

private def polarized (a b : NaturalSpace) : SymmetricPart :=
  rankOne (a+b) - rankOne a - rankOne b

private theorem polarized_apply (a b : NaturalSpace) (i j : Fin 24) :
    (polarized a b).val i j = a i * b j + b i * a j := by
  change (a i+b i)*(a j+b j) - a i*a j - b i*b j = _
  ring

private theorem polarized_smul (a b : NaturalSpace) (s t : ℝ) :
    polarized (s • a) (t • b) = (s*t) • polarized a b := by
  apply Subtype.ext
  ext i j
  simp only [Submodule.coe_smul, Matrix.smul_apply, polarized_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

private theorem polarized_pair (x y : Omega) :
    polarized (pointVector x) (pointVector y) =
      pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y) := by
  apply Subtype.ext
  ext i j
  rw [polarized_apply]
  simp only [pointVector, Pi.single_apply, pairMatrix, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> norm_num <;> tauto

private theorem symmetric_polarized (g : N1) (a b : NaturalSpace) :
    cSymmetric (n1ToC g) (polarized a b) =
      polarized (realLeechRepresentation (n1LeechRepresentation g) a)
        (realLeechRepresentation (n1LeechRepresentation g) b) := by
  change cSymmetric (pullbackToC (n1Pullback g)) _ = _
  rw [cSymmetric_pullback]
  change symmetricLeechRepresentation (n1LeechRepresentation g) (polarized a b) = _
  simp [polarized, symmetricLeechRepresentation_rankOne]

/-- The matrix family uses precisely the existing natural action and marking. -/
theorem cSymmetric_pairMatrix (g : N1) (x y : Omega) :
    cSymmetric (n1ToC g) (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y)) =
      sign (coordinateShift g.val 0 x + coordinateShift g.val 0 y) •
      pairMatrix (coordinateMarking.symm (coordinatePermutation g.val x))
        (coordinateMarking.symm (coordinatePermutation g.val y)) := by
  rw [← polarized_pair, symmetric_polarized, natural_point_sign, natural_point_sign,
    polarized_smul, sign_add, polarized_pair]

/-- Literal inclusion of the matrix branch of Aschbacher 29.10(3). -/
theorem localCompatibility_zero (g : N1) (x y : Omega) (hxy : x ≠ y) :
    cRepresentation (n1ToC g) (eInclusion (literalPair 0 x y hxy)) =
      sign (coordinateShift g.val 0 x + coordinateShift g.val 0 y) •
      eInclusion (literalPair 0 (coordinatePermutation g.val x) (coordinatePermutation g.val y)
        (fun e => hxy ((coordinatePermutation g.val).injective e))) := by
  simp only [literalPair_zero, eInclusion_pairOne]
  rw [cRepresentation_apply]
  change ((n1ToC g).val 0, cShort (n1ToC g) 0, cSymmetric (n1ToC g)
    (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))) = _
  rw [map_zero, map_zero, cSymmetric_pairMatrix, ← map_smul]
  rfl

end Sporadic.Monster.Construction.NMonomial.EAction
