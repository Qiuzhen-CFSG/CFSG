module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Generators
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Faithfulness
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Model
import Mathlib.Tactic.FinCases

/-!
# The literal second ATLAS local subgroup in natural affine coordinates

The exact five-relator presentation has order at most 2880. The literal
four-field affine generators satisfy those relations and generate the
2880-element affine group, identifying that presentation with AGL₂(4).
Its evaluation in the actual ATLAS subgroup is faithful because the cube of
the first generator survives: it is a nonzero translation in the affine
model. This retains the exact two saved generator coordinates and uses no
assumed local isomorphism or native group classification result.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation
open Subgroup Subgroup.CosetWordCertificate

namespace ModelCoordinates
/-- The actual second marked local subgroup of the certified ATLAS model. -/
@[expose] def secondLocalModel : Subgroup Model :=
  closure ({modelGenerator 2,modelGenerator 3} : Set Model)
end ModelCoordinates

namespace FourCoordinates
open ModelCoordinates OrderCertificate Theory.GroupTheory

private theorem modelPair_satisfies :
    Presentation.Satisfies (modelGenerator 2) (modelGenerator 3) := by
  intro i
  have h := modelGenerator_satisfies ⟨i.val+6,by omega⟩
  fin_cases i <;>
    simpa [relatorWord,eval_cons,Presentation.relator,pow_succ,mul_assoc] using h

private instance : Finite Presentation.Carrier := Presentation.finite_card.1
private instance : Finite Affine := Nat.finite_of_card_ne_zero (by rw [affine_card]; decide)

private theorem affineEvaluation_surjective :
    Function.Surjective (Presentation.evaluation pair_satisfies) := by
  apply MonoidHom.range_eq_top.mp
  rw [Presentation.evaluation_range,pair_generates]

private theorem presentation_card : Nat.card Presentation.Carrier = 2880 := by
  apply le_antisymm Presentation.finite_card.2
  rw [←affine_card]
  exact Nat.card_le_card_of_surjective _ affineEvaluation_surjective

private def presentationAffine : Presentation.Carrier ≃* Affine :=
  MulEquiv.ofBijective (Presentation.evaluation pair_satisfies)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨affineEvaluation_surjective,presentation_card.trans affine_card.symm⟩)

private def toSecond : Presentation.Carrier →* secondLocalModel :=
  (MulEquiv.subgroupCongr (Presentation.evaluation_range modelPair_satisfies)).toMonoidHom.comp
    (Presentation.evaluation modelPair_satisfies).rangeRestrict

private theorem toSecond_surjective : Function.Surjective toSecond :=
  (MulEquiv.subgroupCongr (Presentation.evaluation_range modelPair_satisfies)).surjective.comp
    (Presentation.evaluation modelPair_satisfies).rangeRestrict_surjective

private def fromAffine : Affine →* secondLocalModel :=
  toSecond.comp presentationAffine.symm.toMonoidHom

private theorem fromAffine_first : fromAffine first =
    ⟨modelGenerator 2,Subgroup.subset_closure (Set.mem_insert _ _)⟩ := by
  have he : presentationAffine Presentation.a = first := Presentation.evaluation_a pair_satisfies
  rw [←he]
  change toSecond (presentationAffine.symm (presentationAffine _)) = _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact Presentation.evaluation_a modelPair_satisfies

private theorem fromAffine_second : fromAffine second =
    ⟨modelGenerator 3,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ := by
  have he : presentationAffine Presentation.z = second := Presentation.evaluation_z pair_satisfies
  rw [←he]
  change toSecond (presentationAffine.symm (presentationAffine _)) = _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  exact Presentation.evaluation_z modelPair_satisfies

private def fastFirst : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (L0RepWord 1796) * (L1Rep 92 * L2Rep 6)

private theorem fastFirst_eq : embedding (modelGenerator 2) = fastFirst := by
  change L0Rep 1796 * (L1Rep 92 * L2Rep 6) =
    evalWord fastL0Gen (L0RepWord 1796) * (L1Rep 92 * L2Rep 6)
  rw [fastL0Gen_eq]
  rfl

private theorem model_first_cube_ne : (modelGenerator 2)^3 ≠ 1 := by
  intro h
  have he := congrArg (fun x : Model => embedding x (2 : Fin 6156)) h
  rw [map_pow,fastFirst_eq,map_one] at he
  exact (by decide +kernel : (fastFirst^3) (2 : Fin 6156) ≠ 2) he

private theorem fromAffine_injective : Function.Injective fromAffine := by
  apply injective_of_first_cube_ne_one
  intro h
  apply model_first_cube_ne
  have he := congrArg Subtype.val h
  simpa only [fromAffine_first,Subgroup.coe_pow,Subgroup.coe_one] using he

private def affineSecond : Affine ≃* secondLocalModel :=
  MulEquiv.ofBijective fromAffine
    ⟨fromAffine_injective,toSecond_surjective.comp presentationAffine.symm.surjective⟩

/-- The actual second local subgroup has the prescribed natural affine coordinates. -/
def secondLocalEquiv : secondLocalModel ≃* Affine := affineSecond.symm

theorem secondLocalEquiv_first : secondLocalEquiv
    ⟨modelGenerator 2,Subgroup.subset_closure (Set.mem_insert _ _)⟩ = first := by
  apply affineSecond.injective
  exact (affineSecond.apply_symm_apply _).trans fromAffine_first.symm

theorem secondLocalEquiv_second : secondLocalEquiv
    ⟨modelGenerator 3,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ = second := by
  apply affineSecond.injective
  exact (affineSecond.apply_symm_apply _).trans fromAffine_second.symm

theorem secondLocalModel_card : Nat.card secondLocalModel = 2880 :=
  (Nat.card_congr secondLocalEquiv.toEquiv).trans affine_card

end FourCoordinates
end Sporadic.Janko3.AmalgamPresentation
