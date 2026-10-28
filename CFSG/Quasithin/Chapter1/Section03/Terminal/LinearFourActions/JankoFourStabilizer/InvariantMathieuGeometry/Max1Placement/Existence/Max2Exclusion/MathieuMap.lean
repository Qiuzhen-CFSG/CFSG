module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion.QuotientKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.MatrixComparison
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Alignment
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# A derived max2 homomorphism to the concrete Mathieu group

Conjugating the certified row-quotient action, taking inverse transpose, and
conjugating by the second certified basis change sends its two generators into
`TwoCoreLinearModel.actionGroup`. Inverse transpose is multiplicative, so this
constructs a homomorphism on the whole literal source subgroup. Its restriction
to the commutator lands in the ambient derived matrix group, whose central
quotient is already identified with the concrete M₂₂.

The restricted linear map has solvable kernel by the established quotient-kernel
comparison. The kernel after taking the central quotient is the preimage of an
abelian center, and hence is solvable by the extension theorem. No simplicity of
J₄ or equality with the full involution centralizer is needed.

Source motivation: GLS3 Table 5.3i, printed p.270, the `3M₂₂ · 2` factor in the
2A-centralizer. The literal ATLAS word and matrix provenance is retained in the
imported model modules. This supplies the concrete-map input to the max2
exclusion in Aschbacher–Smith A.3.12(17); the exclusion is assembled by its owner.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreCentralizerData.LowerBound
open TwoCoreCentralizerData.OuterImageComparison
open TwoCoreComparison.CoordinateGenerators TwoCoreLinearModel

/-- Inverting and transposing reverse multiplication twice. -/
private def inverseTransposeUnit (u : Matrix12ˣ) : Matrix12ˣ where
  val := (↑u⁻¹ : Matrix12).transpose
  inv := (↑u : Matrix12).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

private def inverseTranspose : Matrix12ˣ ≃* Matrix12ˣ where
  toFun := inverseTransposeUnit
  invFun := inverseTransposeUnit
  left_inv u := Units.ext rfl
  right_inv u := Units.ext rfl
  map_mul' u v := by
    apply Units.ext
    change (↑(u * v)⁻¹ : Matrix12).transpose =
      (↑u⁻¹ : Matrix12).transpose * (↑v⁻¹ : Matrix12).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem inverseTranspose_x : inverseTranspose actionUnitX = rawUnitX := by
  apply Units.ext
  decide +kernel

private theorem inverseTranspose_y : inverseTranspose actionUnitY = rawUnitY := by
  apply Units.ext
  decide +kernel

private def alignQuotient : QuotientMatrixˣ ≃* Matrix12ˣ :=
  ((MulAut.conj changeBasisUnit).trans inverseTranspose).trans (MulAut.conj basisUnit)

private theorem alignQuotient_x :
    alignQuotient quotientX = MulAut.conj basisUnit rawUnitX := by
  change MulAut.conj basisUnit (inverseTranspose
    (changeBasisUnit * quotientX * changeBasisUnit⁻¹)) = _
  rw [← conjugate_x]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right,
    inverseTranspose_x]

private theorem alignQuotient_y :
    alignQuotient quotientY = MulAut.conj basisUnit rawUnitY := by
  change MulAut.conj basisUnit (inverseTranspose
    (changeBasisUnit * quotientY * changeBasisUnit⁻¹)) = _
  rw [← conjugate_y]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right,
    inverseTranspose_y]

private theorem sourceGenerators_closure_eq_top :
    Subgroup.closure {sourceX, sourceY} = ⊤ := by
  apply Subgroup.map_injective sourceSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

private def ambientMap : sourceSubgroup →* Matrix12ˣ :=
  alignQuotient.toMonoidHom.comp quotientMap

private theorem ambientMap_range_le : ambientMap.range ≤ actionGroup := by
  rw [MonoidHom.range_eq_map, ← sourceGenerators_closure_eq_top, MonoidHom.map_closure,
    Set.image_insert_eq, Set.image_singleton]
  apply (closure_le _).mpr
  rintro x (rfl | rfl)
  · change alignQuotient (quotientMap sourceX) ∈ actionGroup
    rw [quotientMap_sourceX, alignQuotient_x]
    exact conjugated_rawX_mem
  · change alignQuotient (quotientMap sourceY) ∈ actionGroup
    rw [quotientMap_sourceY, alignQuotient_y]
    exact conjugated_rawY_mem

attribute [local irreducible] ambientMap alignQuotient inverseTranspose inverseTransposeUnit

private theorem ambientMap_commutator_mem (x : commutator sourceSubgroup) :
    ambientMap x.val ∈ derivedGroup := by
  apply (Subgroup.commutator_mono ambientMap_range_le ambientMap_range_le)
  rw [← map_commutator_eq sourceSubgroup ambientMap]
  exact Subgroup.mem_map_of_mem ambientMap x.property

private def commutatorLinearMap : commutator sourceSubgroup →* derivedGroup :=
  (ambientMap.comp (commutator sourceSubgroup).subtype).codRestrict derivedGroup
    ambientMap_commutator_mem

private theorem commutatorLinearMap_coe (x : commutator sourceSubgroup) :
    (commutatorLinearMap x : Matrix12ˣ) = alignQuotient (quotientMap x.val) := by
  unfold commutatorLinearMap ambientMap
  rfl

attribute [local irreducible] commutatorLinearMap

/-- Restriction and the injective matrix alignment preserve the solvable kernel. -/
private theorem commutatorLinearMap_ker_isSolvable :
    Group.IsSolvable commutatorLinearMap.ker := by
  let : Group.IsSolvable quotientMap.ker := quotientMap_ker_isSolvable
  let f : commutatorLinearMap.ker →* quotientMap.ker :=
    ((commutator sourceSubgroup).subtype.comp commutatorLinearMap.ker.subtype).codRestrict
      quotientMap.ker (by
        intro x
        apply alignQuotient.injective
        rw [map_one]
        change alignQuotient (quotientMap x.val.val) = 1
        rw [← commutatorLinearMap_coe x.val]
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : quotientMap.ker => (z : sourceSubgroup)) h

/-- The derived subgroup of the literal max2 carrier maps to the concrete M₂₂. -/
noncomputable def commutatorMathieuMap : commutator sourceSubgroup →* Sporadic.Mathieu.M22 :=
  derivedQuotientEquivM22.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center derivedGroup)).comp commutatorLinearMap)

/-- Taking the central quotient only adds an abelian layer to the kernel. -/
theorem commutatorMathieuMap_ker_isSolvable : Group.IsSolvable commutatorMathieuMap.ker := by
  have he : commutatorMathieuMap.ker =
      (Subgroup.center derivedGroup).comap commutatorLinearMap := by
    ext x
    change derivedQuotientEquivM22 (QuotientGroup.mk (commutatorLinearMap x)) = 1 ↔
      commutatorLinearMap x ∈ Subgroup.center derivedGroup
    rw [← map_one derivedQuotientEquivM22, derivedQuotientEquivM22.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  let : Group.IsSolvable commutatorLinearMap.ker := commutatorLinearMap_ker_isSolvable
  let : Group.IsSolvable (Subgroup.center derivedGroup) :=
    Group.isSolvable_of_comm (fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp a.property) b.val).symm)
  exact Subgroup.isSolvable_comap_of_solvable_ker commutatorLinearMap
    (Subgroup.center derivedGroup)

/-- The unconditional concrete-map input required by the max2 exclusion. -/
theorem exists_commutatorMathieuMap :
    ∃ f : commutator sourceSubgroup →* Sporadic.Mathieu.M22, Group.IsSolvable f.ker :=
  ⟨commutatorMathieuMap, commutatorMathieuMap_ker_isSolvable⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
