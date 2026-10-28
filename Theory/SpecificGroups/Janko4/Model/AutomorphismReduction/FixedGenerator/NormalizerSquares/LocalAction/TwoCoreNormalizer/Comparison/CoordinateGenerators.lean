module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.QuotientAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Alignment
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl

/-!
# Assembling generators from the raw J₄ two-core coordinates

The raw coordinates, once realized on O₂(C)/Z(O₂(C)), are changed by the
certified matrix P. The two specified words in the literal max2 generators
then have exactly the fixed ATLAS column actions. Reverse word certificates
recover both original generators in the action image. Centralizer control
identifies the kernel of this action with O₂(C), so the new pair generates C
modulo O₂(C).

The final assembly discharges raw-coordinate realization, full generation by
the max2 pair, and the relative normal-closure centralizer bound using their
concrete proofs. Only centralizer control and the order-two center of the
actual two-core remain explicit inputs for the parent to supply.
Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section

open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
open TwoCoreLinearModel

namespace CoordinateGenerators

/-- Apply the certified column basis change to actual quotient coordinates. -/
def changeCoordinates (e : Coordinates) : Coordinates :=
  e.trans (binaryAutMatrix.symm basisUnit)

theorem vector_changeCoordinates (e : Coordinates) (q : involutionTwoCore) :
    vector (changeCoordinates e) q = (basisUnit : Matrix12) *ᵥ vector e q := by
  simpa only [vector, changeCoordinates, MulEquiv.trans_apply,
    ofAdd_toAdd, MulEquiv.apply_symm_apply] using
    (binaryAutMatrix_mulVec (binaryAutMatrix.symm basisUnit) (vector e q)).symm

/-- The public pointwise specification also determines the homomorphism value. -/
theorem localAction_apply (e : Coordinates) (c : involutionCentralizer) :
    localAction e c = matrixAction e (involutionTwoCoreAction c) :=
  localAction_eq_of_mulVec e c _ (matrixAction_mulVec e (involutionTwoCoreAction c))

/-- Changing coordinates conjugates the actual column action. -/
theorem localAction_changeCoordinates (e : Coordinates) (c : involutionCentralizer) :
    localAction (changeCoordinates e) c = MulAut.conj basisUnit (localAction e c) := by
  apply localAction_eq_of_mulVec
  intro q
  rw [vector_changeCoordinates, vector_changeCoordinates]
  have hcancel : ((basisUnit⁻¹ : Matrix12ˣ) : Matrix12) * (basisUnit : Matrix12) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change (((basisUnit : Matrix12) * (localAction e c : Matrix12) *
    ((basisUnit⁻¹ : Matrix12ˣ) : Matrix12)) *ᵥ ((basisUnit : Matrix12) *ᵥ vector e q)) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec (vector e q) ((basisUnit⁻¹ : Matrix12ˣ) : Matrix12)
      (basisUnit : Matrix12), hcancel, Matrix.one_mulVec]
  rw [localAction_apply]
  exact congrArg (fun v => (basisUnit : Matrix12) *ᵥ v)
    (matrixAction_mulVec e (involutionTwoCoreAction c) q)

/-- Centralizer control removes all kernel elements beyond the actual two-core. -/
theorem localAction_ker_le_twoCore (hcent : LocalTwoCoreCentralizerControl)
    [IsExtraspecial 2 involutionTwoCore] (e : Coordinates) :
    (localAction e).ker ≤ involutionTwoCore := by
  intro c hc
  have ha : involutionTwoCoreAction c ∈ (matrixAction e).ker := by
    change localAction e c = 1 at hc
    rw [localAction_apply] at hc
    exact hc
  rw [matrixAction_ker] at ha
  obtain ⟨q, hq⟩ := ha
  have he : involutionTwoCoreAction (c * (q : involutionCentralizer)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change involutionTwoCoreAction c * (MulAut.conj q)⁻¹ = 1
    rw [hq, mul_inv_cancel]
  have hz : c * (q : involutionCentralizer)⁻¹ ∈
      Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) := by
    rw [← involutionTwoCoreAction_ker]
    exact he
  have hm := involutionTwoCore.mul_mem (hcent.1 hz) q.property
  simpa only [inv_mul_cancel_right] using hm

end CoordinateGenerators

open CoordinateGenerators TwoCoreCentralizerData

/-- Conditional assembly after constructing the raw quotient coordinates and
proving full generation of the literal centralizer by the max2 pair. -/
theorem nonempty_actionGenerators_of_rawCoordinates
    (hcent : LocalTwoCoreCentralizerControl)
    (hcenter : Nat.card (Subgroup.center involutionTwoCore) = 2)
    (hgen : localSubgroup = ⊤) (d : RawCoordinates) : Nonempty ActionGenerators := by
  let _ := extraspecial_of_coordinates hcenter d.coordinates
  let e := changeCoordinates d.coordinates
  let f := localAction e
  have hx : f localX = MulAut.conj basisUnit rawUnitX := by
    rw [show f = localAction (changeCoordinates d.coordinates) from rfl,
      localAction_changeCoordinates]
    exact congrArg (MulAut.conj basisUnit)
      (localAction_eq_of_mulVec d.coordinates localX rawUnitX d.actionX)
  have hy : f localY = MulAut.conj basisUnit rawUnitY := by
    rw [show f = localAction (changeCoordinates d.coordinates) from rfl,
      localAction_changeCoordinates]
    exact congrArg (MulAut.conj basisUnit)
      (localAction_eq_of_mulVec d.coordinates localY rawUnitY d.actionY)
  have hfirst : f (firstWord localX localY) = unitC := by
    simpa only [firstWord, map_pow, map_mul, hx, hy] using align_first
  have hsecond : f (secondWord localX localY) = unitD := by
    simpa only [secondWord, map_inv, map_pow, map_mul, hx, hy] using align_second
  have hrange : f.range = actionGroup := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← hgen]
      change (Subgroup.closure ({localX, localY} : Set involutionCentralizer)).map f ≤ _
      rw [MonoidHom.map_closure, Set.image_pair, hx, hy]
      apply (Subgroup.closure_le _).mpr
      rintro u (rfl | rfl)
      · exact conjugated_rawX_mem
      · exact conjugated_rawY_mem
    · apply (Subgroup.closure_le _).mpr
      rintro u (rfl | rfl)
      · exact ⟨firstWord localX localY, hfirst⟩
      · exact ⟨secondWord localX localY, hsecond⟩
  have hgenerate : Subgroup.closure
      ({firstWord localX localY, secondWord localX localY} : Set involutionCentralizer) ⊔
      involutionTwoCore = ⊤ := by
    apply Subgroup.map_injective_of_ker_le f
      ((localAction_ker_le_twoCore hcent e).trans le_sup_right) le_top
    rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair, hfirst, hsecond,
      (Subgroup.map_eq_bot_iff involutionTwoCore).mpr (twoCore_le_localAction_ker e),
      sup_bot_eq, ← MonoidHom.range_eq_map, hrange]
    rfl
  refine ⟨⟨e, firstWord localX localY, secondWord localX localY, hgenerate, ?_, ?_⟩⟩
  · intro q
    have h := matrixAction_mulVec e (involutionTwoCoreAction (firstWord localX localY)) q
    rw [← localAction_apply] at h
    change (f (firstWord localX localY) : Matrix12) *ᵥ vector e q = _ at h
    simpa only [hfirst, coe_unitC, vector] using h
  · intro q
    have h := matrixAction_mulVec e (involutionTwoCoreAction (secondWord localX localY)) q
    rw [← localAction_apply] at h
    change (f (secondWord localX localY) : Matrix12) *ᵥ vector e q = _ at h
    simpa only [hsecond, coe_unitD, vector] using h

/-- Coordinates and generators for the literal two-core quotient action, with
the raw realization and both max2 structural premises discharged. -/
theorem nonempty_actionGenerators
    (hcent : LocalTwoCoreCentralizerControl)
    (hcenter : Nat.card (Subgroup.center involutionTwoCore) = 2) :
    Nonempty ActionGenerators := by
  obtain ⟨d⟩ := nonempty_rawCoordinates hcenter localSubgroup_eq_top
    localNormalClosure_centralizer_pow_two
  exact nonempty_actionGenerators_of_rawCoordinates hcent hcenter localSubgroup_eq_top d

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
