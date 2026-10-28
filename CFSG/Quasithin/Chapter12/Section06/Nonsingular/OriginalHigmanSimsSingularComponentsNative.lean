module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.LocalGeneration
public import Theory.GroupTheory.CentralizerEquivBounds
import all Theory.GroupTheory.CentralizerEquivBounds
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore

/-!
# The intrinsic quotient of a two-central HS involution centralizer

The fixed native centralizer has its actual two-core quotient S₅. Conjugacy
of central Sylow involutions transports that quotient to the centralizer
of the selected native involution. The full centralizer is retained; no
claim about a component of an ambient singular centralizer is made.

Source: the HS local inspection in Aschbacher--Smith 12.6.12, printed
pp.825--826, and GLS3 Table 5.3m. The imported carrier and local quotient
retain their existing ATLAS attribution and kernel certificates.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsSingularComponents
open Sporadic.LeechRelated.HS
open EvenLocalCandidates BlockNormalizer
open EvenLocalCandidates.CentralInvolutionCore

/-- The actual two-central involution centralizer modulo its intrinsic
two-core is S₅, through conjugacy with the marked native local. -/
theorem twoCentral_core_quotient_symmetricFive (j : Carrier)
    (hj : orderOf j = 2) (hc : TwoCentral j) :
    Nonempty (((centralizer ({j} : Set Carrier)) ⧸
      pCore 2 (centralizer ({j} : Set Carrier))) ≃* Equiv.Perm (Fin 5)) := by
  have hzP : e0 ∈ baseSylow :=
    elementary_le_subgroup 0 (subset_closure ⟨0,by simp,rfl⟩)
  have hz : TwoCentral e0 := by
    refine ⟨baseSylow,hzP,mem_center_iff.mpr ?_⟩
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (OrdinaryLocal.first_eq_centralizer ▸ LocalGeneration.sylow_le_member 0 x.property)
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj_of_center_card_two hz
    (fun he => by rw [he,orderOf_one] at hj; omega) e0_nontrivial OrdinaryLocal.sylow_center_card_two)
  let a := MulAut.conj g
  have he : (centralizer ({j} : Set Carrier)).map a.toMonoidHom = localGroup 0 := by
    rw [centralizer_equiv_image,Set.image_singleton]
    change centralizer ({g*j*g⁻¹} : Set Carrier) = _
    rw [hg,←OrdinaryLocal.first_eq_centralizer]
  let d := ((centralizer ({j} : Set Carrier)).equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr he)
  exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans LocalGeneration.firstQuotient⟩

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsSingularComponents
