module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergRecognition
public import Theory.Representation.BinaryAlternatingSixModels.TensorSmallMovement

/-!
# The small-movement Steinberg exclusion on the source section

The original two local planes construct an equivariant Steinberg quotient
of U_L/V. A literal barred involution moving at most two dimensions on
that section would also move at most two on the quotient. The checked
involution tensor bound is at least six, giving a contradiction.

This supplies the representation comparison used twice after abelianness
in 13.8.33, without assuming a tensor quotient or replacing the source
kernel V. The ambient quadratic/centralizer argument supplying small
movement, the local-plane applicability and later permutation/13.4.1
argument remain with qt-d-138-a6-endgame-source.
Source: Aschbacher--Smith, 13.8.33, printed p.967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open BinaryAlternatingSix Theory.SpecificGroups.SymmetricSix
open Representation.BinaryOffender.NaturalTensor
variable {G : Type*} [Group G] [Finite G]
  {L H T L₁ L₂ V V₂ V₃ : Subgroup G}

/-- The actual source local planes are incompatible with an involution
moving at most two dimensions on U_L/V. The Steinberg quotient is derived. -/
theorem source_local_planes_small_involution_impossible
    (d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃)
    (e : (barMap (L ⊔ T) V d.normalizes_V).range ≃* S6)
    (e₁ : ((((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : ((((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (hp : SourceLocalPlanes d e₁ e₂)
    (hP₁ : ∀ g ∈ BinaryFlags.H1, e.symm g ∈
      ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
    (hP₂ : ∀ g ∈ BinaryFlags.H2, e.symm g ∈
      ((L₂ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
    (b : (barMap (L ⊔ T) V d.normalizes_V).range)
    (hb : orderOf (e b) = 2)
    (hsmall : let _ := d.normal; let _ := d.elementary;
      operatorFixedCodim (d.action b) ≤ 2) : False := by
  let _ := d.normal
  let _ := d.elementary
  obtain ⟨q,hq⟩ := source_tensor_quotient d e e₁ e₂ hp hP₁ hP₂
  exact no_tensor_quotient_of_small_involution d.action e b hb hsmall q hq

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
