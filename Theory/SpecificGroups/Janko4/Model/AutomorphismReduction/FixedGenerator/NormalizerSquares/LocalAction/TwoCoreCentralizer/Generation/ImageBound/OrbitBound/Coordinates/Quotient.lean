module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates.Data
/-!
# Coordinates on the canonical homology quotient

The checked contraction NT + TN + SQ = 1 gives every fixed vector a unique
class represented by S times its Q-coordinate. Q annihilates im(N), and QS = 1,
so these maps descend to inverse linear maps on ker(a - 1)/im(a - 1).
The generator calculation uses the actual localHomologyAction and column matrices.
The distinguished natural column maps to coordinate 14.

Source and ATLAS attribution: Tables.lean and ImageBound/source/README.md.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
set_option maxRecDepth 4096

theorem displacement_N (v : NaturalModule) : displacement v = N *ᵥ v := by
  rw [N_eq, Matrix.sub_mulVec, Matrix.one_mulVec, displacement_apply]

def sectionFixed : CoordinateSpace →ₗ[ZMod 2] fixedVectors :=
  S.mulVecLin.codRestrict fixedVectors (by
    intro v
    change displacement (S *ᵥ v) = 0
    rw [displacement_N, Matrix.mulVec_mulVec, N_S, Matrix.zero_mulVec])

def projectionFixed : fixedVectors →ₗ[ZMod 2] CoordinateSpace :=
  Q.mulVecLin.comp fixedVectors.subtype

theorem projection_displacement : displacementInFixed ≤ LinearMap.ker projectionFixed := by
  rintro v ⟨w, hw⟩
  change displacement w = (v : NaturalModule) at hw
  change Q *ᵥ (v : NaturalModule) = 0
  rw [← hw, displacement_N, Matrix.mulVec_mulVec, Q_N, Matrix.zero_mulVec]

/-- The coordinate projection on the literal column quotient. -/
def quotientMap : NaturalHomology →ₗ[ZMod 2] CoordinateSpace :=
  displacementInFixed.liftQ projectionFixed projection_displacement

/-- The classes represented by the last twelve fixed-basis columns. -/
def sectionClass : CoordinateSpace →ₗ[ZMod 2] NaturalHomology :=
  displacementInFixed.mkQ.comp sectionFixed

@[simp] theorem quotientMap_mk (v : fixedVectors) :
    quotientMap (Submodule.Quotient.mk v) = Q *ᵥ (v : NaturalModule) := rfl

@[simp] theorem quotientMap_sectionClass (v : CoordinateSpace) :
    quotientMap (sectionClass v) = v := by
  change Q *ᵥ (S *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, Q_S, Matrix.one_mulVec]

@[simp] theorem sectionClass_quotientMap (v : NaturalHomology) :
    sectionClass (quotientMap v) = v := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    have hv : N *ᵥ (v : NaturalModule) = 0 := by
      rw [← displacement_N]
      exact v.property
    have hc : N *ᵥ (T *ᵥ (v : NaturalModule)) + S *ᵥ (Q *ᵥ (v : NaturalModule)) = v := by
      have he := congrArg (fun M : BinaryMatrix => M *ᵥ (v : NaturalModule)) contraction
      simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
        add_zero, Matrix.one_mulVec] using he
    symm
    apply (Submodule.Quotient.eq displacementInFixed).mpr
    change (v : NaturalModule) - S *ᵥ (Q *ᵥ (v : NaturalModule)) ∈ displacementVectors
    refine ⟨T *ᵥ (v : NaturalModule), ?_⟩
    rw [displacement_N]
    exact eq_sub_iff_add_eq.mpr hc

/-- An actual equivalence between ker(a - 1) / im(a - 1) and twelve binary coordinates. -/
def equiv : NaturalHomology ≃ₗ[ZMod 2] CoordinateSpace :=
  { quotientMap with
    invFun := sectionClass
    left_inv := sectionClass_quotientMap
    right_inv := quotientMap_sectionClass }

theorem equiv_apply (v : NaturalHomology) : equiv v = quotientMap v := rfl

theorem equiv_symm_apply (v : CoordinateSpace) : equiv.symm v = sectionClass v := rfl

theorem sectionClass_seed : sectionClass (vectorOfCode 14) = distinguishedClass := by
  change Submodule.Quotient.mk (sectionFixed (vectorOfCode 14)) =
    Submodule.Quotient.mk distinguishedFixedVector
  congr 1
  apply Subtype.ext
  exact S_seed

theorem equiv_seed : equiv distinguishedClass = vectorOfCode 14 := by
  rw [← sectionClass_seed, equiv_apply, quotientMap_sectionClass]

/-- The two source row lists, decoded as basis images, intertwine the actual column action. -/
theorem equiv_generator (b : Bool) (v : NaturalHomology) :
    equiv ((localHomologyAction (generator b) : Module.End (ZMod 2) NaturalHomology) v) =
      actionMatrix b *ᵥ equiv v := by
  obtain ⟨w, rfl⟩ := equiv.symm.surjective v
  change quotientMap ((homologyAction (generator b).val : Module.End (ZMod 2) NaturalHomology)
    (Submodule.Quotient.mk (sectionFixed w))) = actionMatrix b *ᵥ equiv (equiv.symm w)
  rw [homologyAction_mk, quotientMap_mk, equiv.apply_symm_apply]
  change Q *ᵥ (naturalAction (generator b).val (S *ᵥ w)) = actionMatrix b *ᵥ w
  rw [naturalAction_apply, ← generatorMatrix_eq, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Q_generator_S]
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
