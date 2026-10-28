module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.Orbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Linearization

/-!
# Intrinsic contraction rank on the canonical homology

Contract the actual exterior forms annihilating im(a - 1) with a lift in
ker(a - 1). The resulting rows are covector coordinates under the standard dot
pairing. Their values do not change on adding a displacement, so contraction
descends to NaturalHomology. Pullback permutes the radical for every element of
the entire literal centralizer. Right multiplication by its invertible matrix
identifies the contraction spaces and preserves their dimensions.

This uses the certified ambient generators, not homology-kernel membership or
local generation. The finite identification of a rank fibre with the
specified local orbit is a separate obligation.

Source motivation: GLS3 Table 5.3i, printed p.270; that table asserts no
canonical-homology identification. Matrix provenance and the exterior-space
construction are documented in KernelEquations/source/README.md.
-/

@[expose] public section
open scoped Matrix
set_option maxRecDepth 2048
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank
open KernelBound.OrbitCoverCoordinates
private theorem radical_vanish (R : exteriorRadical displacementVectors)
    (u : fixedVectors) (hu : u ∈ displacementInFixed) (v : NaturalModule) :
    formValue R (u : NaturalModule) v = 0 := R.property.2 u hu v

private theorem coe_fixedAction (c : involutionCentralizer) (u : fixedVectors) :
    (fixedAction c u : NaturalModule) = naturalAction c (u : NaturalModule) := rfl

attribute [local irreducible] exteriorFormSpace exteriorRadical fixedVectors displacementVectors
  displacementInFixed naturalAction fixedAction homologyAction

/-- The exterior forms whose left radical contains the displacement space. -/
abbrev Radical := exteriorRadical displacementVectors

/-- Row coordinates of contraction by a fixed vector. -/
def fixedEvaluation : fixedVectors →ₗ[ZMod 2] (Radical →ₗ[ZMod 2] NaturalModule) where
  toFun u :=
    { toFun R := (u : NaturalModule) ᵥ* (R : BinaryMatrix)
      map_add' R S := Matrix.vecMul_add _ _ _
      map_smul' r R := Matrix.vecMul_smul _ _ _ }
  map_add' u v := by
    apply LinearMap.ext
    intro R
    change ((u : NaturalModule) + (v : NaturalModule)) ᵥ* (R : BinaryMatrix) =
      (u : NaturalModule) ᵥ* (R : BinaryMatrix) + (v : NaturalModule) ᵥ* (R : BinaryMatrix)
    exact Matrix.add_vecMul _ _ _
  map_smul' r u := by
    apply LinearMap.ext
    intro R
    change (r • (u : NaturalModule)) ᵥ* (R : BinaryMatrix) =
      r • ((u : NaturalModule) ᵥ* (R : BinaryMatrix))
    exact Matrix.smul_vecMul _ _ _

theorem fixedEvaluation_displacement : displacementInFixed ≤ fixedEvaluation.ker := by
  intro u hu
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro R
  funext i
  have hz := radical_vanish R u hu (Pi.single i 1)
  change ((u : NaturalModule) ᵥ* (R : BinaryMatrix)) i = 0
  simpa only [formValue, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] using hz

/-- Contraction descends to the actual homology quotient. Rows are coordinates
of covectors under the standard dot pairing. -/
def evaluation : NaturalHomology →ₗ[ZMod 2] (Radical →ₗ[ZMod 2] NaturalModule) :=
  displacementInFixed.liftQ fixedEvaluation fixedEvaluation_displacement

theorem evaluation_mk (u : fixedVectors) (R : Radical) :
    evaluation (Submodule.Quotient.mk u) R = (u : NaturalModule) ᵥ* (R : BinaryMatrix) := rfl

/-- The rows represent precisely the covectors in the intrinsic construction. -/
theorem evaluation_mk_pairing (u : fixedVectors) (R : Radical) (v : NaturalModule) :
    evaluation (Submodule.Quotient.mk u) R ⬝ᵥ v = formValue R (u : NaturalModule) v := by
  rw [evaluation_mk, formValue, Matrix.dotProduct_mulVec]

/-- The row space of covectors obtained by contraction. -/
def space (h : NaturalHomology) : Submodule (ZMod 2) NaturalModule :=
  (evaluation h).range

/-- Dimension of the contraction space, independent of the chosen lift. -/
noncomputable def rank (h : NaturalHomology) : ℕ := Module.finrank (ZMod 2) (space h)

/-- Ambient group membership supplies radical preservation for the whole centralizer. -/
theorem centralizer_preserves_radical (c : involutionCentralizer) :
    (c : BinaryMatrixˣ) ∈ formStabilizer Radical := by
  apply mem_formStabilizer_exteriorRadical
  · exact matrixGroup_le_formStabilizer exteriorFormSpace
      matrixUnitA_mem_exteriorFormStabilizer matrixUnitB_mem_exteriorFormStabilizer
      (involutionCentralizer_le_matrixGroup c.property)
  · intro u hu
    have hv : naturalAction c u ∈ displacementVectors := displacementVectors_invariant c hu
    rw [naturalAction_apply] at hv
    exact hv
  · intro u hu
    have hv : naturalAction c⁻¹ u ∈ displacementVectors := displacementVectors_invariant c⁻¹ hu
    rw [naturalAction_apply] at hv
    exact hv

private def pullbackLinear (c : involutionCentralizer) : Radical →ₗ[ZMod 2] Radical where
  toFun R := ⟨formPullback (c : BinaryMatrixˣ) R,
    (centralizer_preserves_radical c R).mpr R.property⟩
  map_add' R S := by
    apply Subtype.ext
    change formPullback _ (↑R + ↑S) = formPullback _ ↑R + formPullback _ ↑S
    simp only [formPullback, Matrix.mul_add, Matrix.add_mul]
  map_smul' r R := by
    apply Subtype.ext
    change formPullback _ (r • (R : BinaryMatrix)) = r • formPullback _ ↑R
    simp only [formPullback, Matrix.mul_smul, Matrix.smul_mul]

private theorem pullbackLinear_surjective (c : involutionCentralizer) :
    Function.Surjective (pullbackLinear c) := by
  intro R
  refine ⟨pullbackLinear c⁻¹ R, ?_⟩
  apply Subtype.ext
  change formPullback (c : BinaryMatrixˣ) (formPullback (c⁻¹ : BinaryMatrixˣ) R) = R
  rw [← formPullback_mul]
  simp only [inv_mul_cancel, formPullback_one]

private def rowEquiv (g : BinaryMatrixˣ) : NaturalModule ≃ₗ[ZMod 2] NaturalModule where
  toFun u := u ᵥ* (g : BinaryMatrix)
  invFun u := u ᵥ* ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix)
  left_inv u := by dsimp only; rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv u := by dsimp only; rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  map_add' u v := Matrix.add_vecMul _ _ _
  map_smul' r u := Matrix.smul_vecMul _ _ _

private theorem evaluation_transport (c : involutionCentralizer) (h : NaturalHomology) :
    (rowEquiv (c : BinaryMatrixˣ)).toLinearMap.comp
        (evaluation ((homologyAction c : Module.End (ZMod 2) NaturalHomology) h)) =
      (evaluation h).comp (pullbackLinear c) := by
  induction h using Submodule.Quotient.induction_on with
  | H u =>
    apply LinearMap.ext
    intro R
    change evaluation ((homologyAction c : Module.End (ZMod 2) NaturalHomology)
      (Submodule.Quotient.mk u)) R ᵥ* (c : BinaryMatrixˣ).val = _
    rw [homologyAction_mk, evaluation_mk, coe_fixedAction]
    change (naturalAction c (u : NaturalModule)) ᵥ* (R : BinaryMatrix) ᵥ*
      (c : BinaryMatrixˣ).val = (u : NaturalModule) ᵥ* formPullback (c : BinaryMatrixˣ) R
    rw [naturalAction_apply, Matrix.vecMul_mulVec, Matrix.vecMul_vecMul]
    rfl

private theorem space_transport (c : involutionCentralizer) (h : NaturalHomology) :
    (space ((homologyAction c : Module.End (ZMod 2) NaturalHomology) h)).map
        (rowEquiv (c : BinaryMatrixˣ)).toLinearMap = space h := by
  change (evaluation ((homologyAction c : Module.End (ZMod 2) NaturalHomology) h)).range.map _ =
    (evaluation h).range
  rw [← LinearMap.range_comp, evaluation_transport]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (pullbackLinear_surjective c))

/-- Every element of the full literal centralizer preserves contraction rank. -/
theorem rank_invariant (c : involutionCentralizer) (h : NaturalHomology) :
    rank ((homologyAction c : Module.End (ZMod 2) NaturalHomology) h) = rank h := by
  exact ((rowEquiv (c : BinaryMatrixˣ)).finrank_map_eq
    (space ((homologyAction c : Module.End (ZMod 2) NaturalHomology) h))).symm.trans
      (congrArg (fun P : Submodule (ZMod 2) NaturalModule => Module.finrank (ZMod 2) P)
        (space_transport c h))

theorem rank_zero : rank (0 : NaturalHomology) = 0 := by
  have hz : evaluation (0 : NaturalHomology) = 0 := evaluation.map_zero
  have hs : space (0 : NaturalHomology) = ⊥ :=
    (congrArg LinearMap.range hz).trans LinearMap.range_zero
  exact (congrArg (fun P : Submodule (ZMod 2) NaturalModule =>
    Module.finrank (ZMod 2) P) hs).trans (finrank_bot (ZMod 2) NaturalModule)

/-- Rank is constant on the actual local orbit, by the full-centralizer theorem. -/
theorem rank_eq_seed_of_mem_orbit (h : NaturalHomology) (hh : h ∈ distinguishedOrbit) :
    rank h = rank distinguishedClass := by
  obtain ⟨g, rfl⟩ := hh
  exact rank_invariant (g : involutionCentralizer) distinguishedClass

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.ContractionRank
