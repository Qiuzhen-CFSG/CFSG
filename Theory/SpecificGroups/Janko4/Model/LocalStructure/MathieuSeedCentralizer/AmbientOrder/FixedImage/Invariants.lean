module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.Quadratic

/-!
# Ambient invariants restricted to the literal seed fixed space

The ambient quadratic form and exterior-form space are certified for both
original generators. Their restrictions are therefore preserved by every actor
of the FULL seed centralizer, with no local-subgroup containment assumption.
Pullback is a right action on forms; the linear actions themselves are the
original left-column actions from `FixedAction`.

`invariantStabilizer` is an explicitly defined finite overgroup of the action
image. No numerical bound for this overgroup is asserted here. In particular,
the old first-involution homology quotient is not used for the present seed.

Matrix provenance: `Model.Data` and `Cardinality.Subgroup`. The invariant
certificates and their source references are in `KernelEquations.ExteriorInvariance`
and `OrbitInvariance.Quadratic`. GLS3 Table 5.3i is motivation only.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
open KernelBound.OrbitCoverCoordinates

abbrev Form := AmbientOrder.fixedVectors → AmbientOrder.fixedVectors → ZMod 2

/-- Restriction of an ambient bilinear matrix to the actual fixed columns. -/
def restriction : BinaryMatrix →ₗ[ZMod 2] Form where
  toFun R u v := (u : AmbientOrder.NaturalModule) ⬝ᵥ R *ᵥ (v : AmbientOrder.NaturalModule)
  map_add' R S := by
    funext u v
    exact (congrArg (fun w => (u : AmbientOrder.NaturalModule) ⬝ᵥ w)
      (Matrix.add_mulVec R S v)).trans (dotProduct_add _ _ _)
  map_smul' r R := by
    funext u v
    exact (congrArg (fun w => (u : AmbientOrder.NaturalModule) ⬝ᵥ w)
      (Matrix.smul_mulVec r R v)).trans (dotProduct_smul _ _ _)

/-- The image of the certified ambient exterior space under restriction. -/
def exteriorSpace : Submodule (ZMod 2) Form := exteriorFormSpace.map restriction

/-- The certified ambient quadratic function, restricted to fixed columns. -/
def quadraticValue (u : AmbientOrder.fixedVectors) : ZMod 2 := OrbitQuadratic.value u

abbrev Actor := (Module.End (ZMod 2) AmbientOrder.fixedVectors)ˣ

instance actorFinite : Finite Actor :=
  Finite.of_injective (fun g : Actor => (g.val : AmbientOrder.fixedVectors → AmbientOrder.fixedVectors))
    (by intro g h he; exact Units.ext (LinearMap.ext (congrFun he)))

def pullback (g : Actor) (R : Form) : Form := fun u v => R (g.val u) (g.val v)

theorem pullback_one (R : Form) : pullback 1 R = R := rfl

theorem pullback_mul (g h : Actor) (R : Form) :
    pullback (g * h) R = pullback h (pullback g R) := rfl

theorem pullback_restriction (c : Centralizer) (R : BinaryMatrix) :
    pullback (AmbientOrder.fixedAction c) (restriction R) =
      restriction (formPullback (toAmbient (c : Model)) R) := by
  funext u v
  change ((AmbientOrder.naturalAction c u) : AmbientOrder.NaturalModule) ⬝ᵥ R *ᵥ
    (AmbientOrder.naturalAction c v) =
      (u : AmbientOrder.NaturalModule) ⬝ᵥ formPullback (toAmbient (c : Model)) R *ᵥ
        (v : AmbientOrder.NaturalModule)
  simp only [AmbientOrder.naturalAction_apply, formPullback, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec (u : AmbientOrder.NaturalModule), Matrix.vecMul_transpose]
  rfl

theorem quadraticValue_invariant (c : Centralizer) (u : AmbientOrder.fixedVectors) :
    quadraticValue ((AmbientOrder.fixedAction c).val u) = quadraticValue u := by
  exact OrbitQuadratic.value_matrixGroup (toAmbient (c : Model)) (c : Model).property u

private theorem exteriorSpace_forward (c : Centralizer) (R : Form)
    (hR : R ∈ exteriorSpace) : pullback (AmbientOrder.fixedAction c) R ∈ exteriorSpace := by
  obtain ⟨S, hS, rfl⟩ := hR
  rw [pullback_restriction]
  refine ⟨formPullback (toAmbient (c : Model)) S, ?_, rfl⟩
  exact (matrixGroup_le_formStabilizer exteriorFormSpace
    matrixUnitA_mem_exteriorFormStabilizer matrixUnitB_mem_exteriorFormStabilizer
    (c : Model).property S).mpr hS

theorem exteriorSpace_invariant (c : Centralizer) (R : Form) :
    pullback (AmbientOrder.fixedAction c) R ∈ exteriorSpace ↔ R ∈ exteriorSpace := by
  constructor
  · intro h
    have he := exteriorSpace_forward c⁻¹ _ h
    rw [← pullback_mul, ← map_mul, mul_inv_cancel, map_one, pullback_one] at he
    exact he
  · exact exteriorSpace_forward c R

/-- All fixed-space linear automorphisms preserving these two restrictions. -/
def invariantStabilizer : Subgroup Actor where
  carrier := {g | (∀ u, quadraticValue (g.val u) = quadraticValue u) ∧
    ∀ R, pullback g R ∈ exteriorSpace ↔ R ∈ exteriorSpace}
  one_mem' := ⟨fun _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨hgq, hge⟩ ⟨hhq, hhe⟩
    constructor
    · intro u
      exact (hgq (h.val u)).trans (hhq u)
    · intro R
      rw [pullback_mul]
      exact (hhe _).trans (hge R)
  inv_mem' := by
    rintro g ⟨hgq, hge⟩
    constructor
    · intro u
      have he := hgq (g⁻¹.val u)
      have hu : g.val (g⁻¹.val u) = u := by
        change ((g * g⁻¹).val) u = u
        rw [mul_inv_cancel]
        rfl
      rw [hu] at he
      exact he.symm
    · intro R
      have he := hge (pullback g⁻¹ R)
      rw [← pullback_mul, inv_mul_cancel, pullback_one] at he
      exact he.symm

/-- This inclusion applies to every actor in the full ambient centralizer. -/
theorem fixedAction_range_le_invariantStabilizer :
    AmbientOrder.fixedAction.range ≤ invariantStabilizer := by
  rintro g ⟨c, rfl⟩
  exact ⟨quadraticValue_invariant c, exteriorSpace_invariant c⟩

theorem fixedAction_image_card_le_invariantStabilizer :
    Nat.card AmbientOrder.fixedAction.range ≤ Nat.card invariantStabilizer :=
  Nat.card_le_card_of_injective
    (Subgroup.inclusion fixedAction_range_le_invariantStabilizer)
    (Subgroup.inclusion_injective fixedAction_range_le_invariantStabilizer)

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
