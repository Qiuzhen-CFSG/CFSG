module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Coordinates
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SourceComparisons
public import Theory.SpecificGroups.Monster.Construction.LocalC.N1Embedding

/-!
# The genuine N1 action on the two literal tensor slots

The natural coordinate marking and tensor distribution identify the source
natural-by-direct-sum representation with the published second and third
slots. Its action agrees on every vector with the literal LocalC map after
tensorSplitting. This comparison proves form preservation and triviality on K;
the actual spin action supplies both odd first-generator formulas on all
Parker parameters. No odd short-family comparison is used.

Source: Aschbacher, *Sporadic Groups*, Sections 27 and 29, especially the two
maps preceding 29.8 on printed p. 157. Extending this action to all three
summands under N is a separate construction.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC TrialitySpin SpinActions SignedModules
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction


/-- The marked source comparison for the two literal tensor slots. -/
def sourcePairCoordinates : TensorAction.DirectSumSpace ≃ₗ[ℝ] (TensorTwo × TensorThree) :=
  (TensorProduct.congr naturalLeechComparison (LinearEquiv.refl ℝ SpinDirectSum)).trans
    (TensorProduct.prodRight ℝ ℝ NaturalSpace B1A2 B1A3)

theorem sourcePairCoordinates_tmul (a : Natural.B1_24) (s : SpinDirectSum) :
    sourcePairCoordinates (a ⊗ₜ[ℝ] s) =
      (naturalLeechComparison a ⊗ₜ[ℝ] s.1, naturalLeechComparison a ⊗ₜ[ℝ] s.2) := rfl

theorem sourcePairCoordinates_restriction (v : TensorAction.Space) :
    sourcePairCoordinates (TensorAction.restriction v) =
      tensorSplitting (naturalTensorComparison v) := by
  have h : sourcePairCoordinates.toLinearMap.comp TensorAction.restriction.toLinearMap =
      tensorSplitting.toLinearMap.comp naturalTensorComparison.toLinearMap := by
    apply TensorProduct.ext'
    intro a s
    rfl
  exact LinearMap.congr_fun h v

/-- The genuine N1 representation on the two literal tensor slots. -/
def pairRepresentation : Representation ℝ N1 (TensorTwo × TensorThree) :=
  sourcePairCoordinates.conjRingEquiv.toMonoidHom.comp TensorAction.directSumRepresentation

theorem pairRepresentation_source (g : N1) (v : TensorAction.DirectSumSpace) :
    pairRepresentation g (sourcePairCoordinates v) =
      sourcePairCoordinates (TensorAction.directSumRepresentation g v) := by
  change sourcePairCoordinates (TensorAction.directSumRepresentation g
    (sourcePairCoordinates.symm (sourcePairCoordinates v))) = _
  rw [sourcePairCoordinates.symm_apply_apply]

/-- Both slots are compared with the literal LocalC map on every vector, with no odd-family input. -/
theorem pairRepresentation_localC (g : N1) (v : TensorTwo × TensorThree) :
    pairRepresentation g v =
      tensorSplitting ((n1ToC g).val (tensorSplitting.symm v)) := by
  obtain ⟨w,rfl⟩ := sourcePairCoordinates.surjective v
  obtain ⟨u,rfl⟩ := TensorAction.restriction.surjective w
  rw [pairRepresentation_source, ← TensorAction.restriction_equivariant,
    sourcePairCoordinates_restriction, sourcePairCoordinates_restriction,
    tensorSplitting.symm_apply_apply, n1ToC_intertwines]

theorem pairRepresentation_isometry (g : N1) (v w : TensorTwo × TensorThree) :
    tensorPairForm (pairRepresentation g v) (pairRepresentation g w) = tensorPairForm v w := by
  rw [pairRepresentation_localC, pairRepresentation_localC, tensorSplitting_isometry,
    c_preserves_minusForm, ← tensorSplitting_isometry,
    tensorSplitting.apply_symm_apply, tensorSplitting.apply_symm_apply]

theorem pairRepresentation_K (g : N1) (hg : g.val ∈ TrialitySpin.K) : pairRepresentation g = 1 := by
  have he : n1ToC g = 1 := by
    have hk : g ∈ n1ToC.ker := by
      rw [n1ToC_kernel]
      exact hg
    exact hk
  apply LinearMap.ext
  intro v
  rw [pairRepresentation_localC, he]
  exact tensorSplitting.apply_symm_apply v

/-- The actual source NPlus action on the two displayed tensor factors. -/
theorem pairRepresentation_even_tmul (g : NPlus) (a : Natural.B1_24) (s : SpinDirectSum) :
    pairRepresentation (HalfActions.inclusion g)
      (naturalLeechComparison a ⊗ₜ[ℝ] s.1, naturalLeechComparison a ⊗ₜ[ℝ] s.2) =
      (naturalLeechComparison (NaturalAction.representation (HalfActions.inclusion g) a) ⊗ₜ[ℝ]
        HalfActions.secondRepresentation g s.1,
       naturalLeechComparison (NaturalAction.representation (HalfActions.inclusion g) a) ⊗ₜ[ℝ]
        HalfActions.thirdRepresentation g s.2) := by
  rw [← sourcePairCoordinates_tmul, pairRepresentation_source]
  change sourcePairCoordinates
    (NaturalAction.representation (HalfActions.inclusion g) a ⊗ₜ[ℝ]
      DirectSumAction.representation (HalfActions.inclusion g) s) = _
  rw [DirectSumAction.representation_even, sourcePairCoordinates_tmul]

/-- All Parker parameters for the odd first automorphism, in the literal second slot. -/
theorem pairRepresentation_odd_two (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (b : ParkerLoop) :
    pairRepresentation (DirectSumAction.standard α) (pointVector x ⊗ₜ[ℝ] delta2 b,0) =
      (0,pointVector ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        delta3 (parkerSign (golayQuarterWeight b.1) (α.val b))) := by
  have hv : sourcePairCoordinates (Natural.L 0 1 x ⊗ₜ[ℝ] (delta2 b,0)) =
      (pointVector x ⊗ₜ[ℝ] delta2 b,0) := by
    rw [sourcePairCoordinates_tmul, naturalLeechComparison_L_one, TensorProduct.tmul_zero]
    rfl
  rw [← hv, pairRepresentation_source]
  change sourcePairCoordinates (NaturalAction.representation (DirectSumAction.standard α)
    (Natural.L 0 1 x) ⊗ₜ[ℝ] DirectSumAction.representation (DirectSumAction.standard α) (delta2 b,0)) = _
  rw [NaturalAction.representation_standard_L, DirectSumAction.representation_odd_delta2 α hα,
    sourcePairCoordinates_tmul, naturalLeechComparison_L_one, TensorProduct.tmul_zero]
  rfl

/-- The inverse-axis counterpart, on all third-slot Parker vectors. -/
theorem pairRepresentation_odd_three (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (b : ParkerLoop) :
    pairRepresentation (DirectSumAction.standard α) (0,pointVector x ⊗ₜ[ℝ] delta3 b) =
      (pointVector ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        delta2 (parkerSign (golayQuarterWeight b.1) (α.val b)),0) := by
  have hv : sourcePairCoordinates (Natural.L 0 1 x ⊗ₜ[ℝ] (0,delta3 b)) =
      (0,pointVector x ⊗ₜ[ℝ] delta3 b) := by
    rw [sourcePairCoordinates_tmul, naturalLeechComparison_L_one, TensorProduct.tmul_zero]
    rfl
  rw [← hv, pairRepresentation_source]
  change sourcePairCoordinates (NaturalAction.representation (DirectSumAction.standard α)
    (Natural.L 0 1 x) ⊗ₜ[ℝ] DirectSumAction.representation (DirectSumAction.standard α) (0,delta3 b)) = _
  rw [NaturalAction.representation_standard_L, DirectSumAction.representation_odd_delta3 α hα,
    sourcePairCoordinates_tmul, naturalLeechComparison_L_one, TensorProduct.tmul_zero]
  rfl


end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction
