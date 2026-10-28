module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.CentralField
public import Theory.Representation.Mathieu.M22James.Unitary

/-!
# Unitary structure of the unique triple Mathieu module

James uniqueness gives an actual binary equivalence with the native matrix
module. Intertwining the distinguished central element makes that same map
linear over the specific four-element field constructed in `CentralField`.
Pulling back the native Hermitian and quadratic forms proves nondegeneracy,
invariance, and the identity `algebraMap (q v) = f v v` on the original carrier.

The same equivalence supplies coordinates in the literal special unitary
group SU₆(2). Both the original group operators and the chosen central scalars
are intertwined, and the form becomes the standard Hermitian form in those
coordinates. No additional representation or form-existence hypothesis remains.

`source_lemma_H_12_1_2` specializes this construction to the canonical module
of H.12.1(1). The arbitrary-module statements are used by `LocalInput` for
the ambient restriction and the subsequent local geometry.

Source: Aschbacher–Smith H.12.1(1–2), printed pp.393–394 (PDF pp.404–405).
The imported native realization retains the attribution of its ATLAS data.
-/

@[expose] public section
noncomputable section
open Representation Sporadic.Mathieu
open scoped Matrix
open Representation.SL2FourNatural (fieldFrobenius)
namespace CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22
namespace UnitaryModel
abbrev F := FieldModel.F
variable {L W : Type*} [Group L] [Finite L] [AddCommGroup W] [Module (ZMod 2) W]
  (hL : IsTripleM22 L) (ρ : Representation (ZMod 2) L W)
  (hf : Function.Injective ρ) [ρ.IsIrreducible]
  (hd : Module.finrank (ZMod 2) W = 12)

local instance : Module F M22TripleCover.BinarySpace :=
  M22TripleCover.Uniqueness.PointRestriction.fieldModule
    M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful

/-- James uniqueness as a chosen actual intertwiner on the original binary carrier. -/
def binaryEquiv : Representation.Equiv ρ hL.binaryRepresentation :=
  Classical.choice (hL.equiv_binaryRepresentation_of_finrank_twelve ρ hf hd)

/-- The binary intertwiner is linear for the specified central-field structures. -/
def modelEquiv : letI := FieldModel.moduleStructure hL ρ hf
    W ≃ₗ[F] M22TripleCover.BinarySpace := by
  letI := FieldModel.moduleStructure hL ρ hf
  refine { (binaryEquiv hL ρ hf hd).toLinearEquiv.toAddEquiv with map_smul' := ?_ }
  intro a v
  change binaryEquiv hL ρ hf hd (a.re • v + a.im • ρ hL.centralScalar v) =
    a.re • binaryEquiv hL ρ hf hd v +
      a.im • M22TripleCover.binaryRepresentation M22TripleCover.scalar
        (binaryEquiv hL ρ hf hd v)
  rw [map_add, map_smul, map_smul]
  have he := LinearMap.congr_fun ((binaryEquiv hL ρ hf hd).isIntertwining'
    hL.centralScalar) v
  change binaryEquiv hL ρ hf hd (ρ hL.centralScalar v) =
    hL.binaryRepresentation hL.centralScalar (binaryEquiv hL ρ hf hd v) at he
  rw [hL.binaryRepresentation_centralScalar] at he
  rw [he]

theorem modelEquiv_apply (v : W) :
    modelEquiv hL ρ hf hd v = binaryEquiv hL ρ hf hd v := rfl

theorem modelEquiv_intertwines (g : L) (v : W) :
    modelEquiv hL ρ hf hd (ρ g v) =
      M22TripleCover.binaryRepresentation (hL.groupEquiv g) (modelEquiv hL ρ hf hd v) :=
  LinearMap.congr_fun ((binaryEquiv hL ρ hf hd).isIntertwining' g) v

/-- Pullback of the native nondegenerate Hermitian form through that field equivalence. -/
def hermitianForm : letI := FieldModel.moduleStructure hL ρ hf
    W →ₗ[F] W →ₛₗ[fieldFrobenius.toRingHom] F := by
  letI := FieldModel.moduleStructure hL ρ hf
  exact (M22TripleCover.Unitary.hermitianForm.comp (modelEquiv hL ρ hf hd).toLinearMap).compl₂
    (modelEquiv hL ρ hf hd).toLinearMap

theorem hermitianForm_apply (v w : W) :
    hermitianForm hL ρ hf hd v w =
      M22TripleCover.Unitary.hermitianForm (modelEquiv hL ρ hf hd v)
        (modelEquiv hL ρ hf hd w) := rfl

theorem hermitianForm_symmetry (v w : W) :
    fieldFrobenius (hermitianForm hL ρ hf hd v w) = hermitianForm hL ρ hf hd w v :=
  M22TripleCover.Unitary.hermitianForm_symmetry _ _

theorem hermitianForm_nondegenerate : letI := FieldModel.moduleStructure hL ρ hf
    (hermitianForm hL ρ hf hd).Nondegenerate := by
  let := FieldModel.moduleStructure hL ρ hf
  constructor
  · intro v hv
    apply (modelEquiv hL ρ hf hd).injective
    rw [map_zero]
    apply M22TripleCover.Unitary.hermitianForm_nondegenerate.1
    intro w
    obtain ⟨u, rfl⟩ := (modelEquiv hL ρ hf hd).surjective w
    exact hv u
  · intro v hv
    apply (modelEquiv hL ρ hf hd).injective
    rw [map_zero]
    apply M22TripleCover.Unitary.hermitianForm_nondegenerate.2
    intro w
    obtain ⟨u, rfl⟩ := (modelEquiv hL ρ hf hd).surjective w
    exact hv u

theorem hermitianForm_invariant (g : L) (v w : W) :
    hermitianForm hL ρ hf hd (ρ g v) (ρ g w) = hermitianForm hL ρ hf hd v w := by
  simp only [hermitianForm_apply, modelEquiv_intertwines,
    M22TripleCover.Unitary.hermitianForm_invariant]

/-- The native binary quadratic diagonal pulled back along the same equivalence. -/
def quadraticForm : QuadraticForm (ZMod 2) W :=
  M22TripleCover.Unitary.quadraticForm.comp (binaryEquiv hL ρ hf hd).toLinearEquiv.toLinearMap

theorem quadraticForm_diagonal (v : W) :
    algebraMap (ZMod 2) F (quadraticForm hL ρ hf hd v) = hermitianForm hL ρ hf hd v v :=
  M22TripleCover.Unitary.quadraticForm_diagonal _

theorem quadraticForm_invariant (g : L) (v : W) :
    quadraticForm hL ρ hf hd (ρ g v) = quadraticForm hL ρ hf hd v := by
  change M22TripleCover.Unitary.quadraticForm (modelEquiv hL ρ hf hd (ρ g v)) = _
  rw [modelEquiv_intertwines, M22TripleCover.Unitary.quadraticForm_invariant]
  rfl

/-- A faithful homomorphism to the literal special-unitary group of the standard form. -/
def unitaryAction : L →* Theory.SpecificGroups.U6Two.form.specialSubgroup :=
  M22TripleCover.Unitary.unitaryAction.comp hL.groupEquiv.toMonoidHom

theorem unitaryAction_faithful : Function.Injective (unitaryAction hL) :=
  M22TripleCover.Unitary.unitaryAction_faithful.comp hL.groupEquiv.injective

/-- Binary coordinates intertwining the original action with the actual unitary matrices. -/
def standardCoordinates : W ≃ₗ[ZMod 2] (Fin 6 → Theory.SpecificGroups.U6Two.Field) :=
  (binaryEquiv hL ρ hf hd).toLinearEquiv.trans M22TripleCover.Unitary.standardCoordinates

/-- The coordinates preserve the specified central scalars through the fixed field isomorphism. -/
theorem standardCoordinates_smul (a : F) (v : W) :
    letI := FieldModel.moduleStructure hL ρ hf
    standardCoordinates hL ρ hf hd (a • v) =
      Representation.SL2FourNatural.fieldEquiv a • standardCoordinates hL ρ hf hd v := by
  let := FieldModel.moduleStructure hL ρ hf
  change M22TripleCover.Unitary.standardCoordinates (modelEquiv hL ρ hf hd (a • v)) = _
  rw [map_smul, M22TripleCover.Unitary.standardCoordinates_smul]
  rfl

/-- Equality of the literal column actions for every original vector. -/
theorem unitaryAction_intertwines (g : L) (v : W) :
    ((unitaryAction hL g).val : Matrix (Fin 6) (Fin 6) Theory.SpecificGroups.U6Two.Field) *ᵥ
      standardCoordinates hL ρ hf hd v = standardCoordinates hL ρ hf hd (ρ g v) := by
  change _ = M22TripleCover.Unitary.standardCoordinates (modelEquiv hL ρ hf hd (ρ g v))
  rw [modelEquiv_intertwines]
  exact M22TripleCover.Unitary.unitaryAction_intertwines _ _

/-- The transported form is the standard unitary form in the same coordinates. -/
theorem standardCoordinates_form (v w : W) :
    Representation.SL2FourNatural.fieldEquiv (hermitianForm hL ρ hf hd v w) =
      standardCoordinates hL ρ hf hd v ⬝ᵥ
        (fun i => Theory.SpecificGroups.U6Two.conjugation
          (standardCoordinates hL ρ hf hd w i)) :=
  M22TripleCover.Unitary.standardCoordinates_form _ _

include hd in
/-- The two invariant forms on any faithful irreducible module of binary dimension twelve. -/
theorem invariant_forms_exist :
    letI := FieldModel.moduleStructure hL ρ hf
    ∃ (f : W →ₗ[F] W →ₛₗ[fieldFrobenius.toRingHom] F)
      (q : QuadraticForm (ZMod 2) W),
      f.Nondegenerate ∧
      (∀ v w, fieldFrobenius (f v w) = f w v) ∧
      (∀ g v w, f (ρ g v) (ρ g w) = f v w) ∧
      (∀ v, algebraMap (ZMod 2) F (q v) = f v v) ∧
      (∀ g v, q (ρ g v) = q v) :=
  ⟨hermitianForm hL ρ hf hd, quadraticForm hL ρ hf hd,
    hermitianForm_nondegenerate hL ρ hf hd, hermitianForm_symmetry hL ρ hf hd,
    hermitianForm_invariant hL ρ hf hd, quadraticForm_diagonal hL ρ hf hd,
    quadraticForm_invariant hL ρ hf hd⟩

end UnitaryModel
end CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22

namespace CFSG.Quasithin.ChapterH.Section10To12
open Sporadic.Mathieu
open IsTripleM22

/-- H.12.1(2): the unique binary module carries a faithful six-dimensional F₄-action
whose scalar restriction is the original action, together with a nondegenerate invariant
Hermitian form and its invariant binary quadratic diagonal. -/
theorem source_lemma_H_12_1_2 {L : Type*} [Group L] [Finite L] (hL : IsTripleM22 L) :
    letI := FieldModel.moduleStructure hL hL.binaryRepresentation hL.binaryRepresentation_faithful
    letI := FieldModel.tower hL hL.binaryRepresentation hL.binaryRepresentation_faithful
    Module.finrank FieldModel.F M22TripleCover.BinarySpace = 6 ∧
    Function.Injective (FieldModel.representation hL hL.binaryRepresentation
      hL.binaryRepresentation_faithful) ∧
    Nonempty (Representation.Equiv
      (Representation.restrictScalars (k := ZMod 2)
        (FieldModel.representation hL hL.binaryRepresentation hL.binaryRepresentation_faithful))
      hL.binaryRepresentation) ∧
    ∃ (f : M22TripleCover.BinarySpace →ₗ[FieldModel.F]
          M22TripleCover.BinarySpace →ₛₗ[fieldFrobenius.toRingHom] FieldModel.F)
      (q : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace),
      f.Nondegenerate ∧
      (∀ v w, fieldFrobenius (f v w) = f w v) ∧
      (∀ g v w, f (hL.binaryRepresentation g v) (hL.binaryRepresentation g w) = f v w) ∧
      (∀ v, algebraMap (ZMod 2) FieldModel.F (q v) = f v v) ∧
      (∀ g v, q (hL.binaryRepresentation g v) = q v) := by
  refine ⟨FieldModel.finrank hL hL.binaryRepresentation hL.binaryRepresentation_faithful
      M22TripleCover.binarySpace_finrank,
    FieldModel.faithful hL hL.binaryRepresentation hL.binaryRepresentation_faithful,
    ⟨FieldModel.restrictionEquiv hL hL.binaryRepresentation hL.binaryRepresentation_faithful⟩, ?_⟩
  exact UnitaryModel.invariant_forms_exist hL hL.binaryRepresentation
    hL.binaryRepresentation_faithful M22TripleCover.binarySpace_finrank

end CFSG.Quasithin.ChapterH.Section10To12
