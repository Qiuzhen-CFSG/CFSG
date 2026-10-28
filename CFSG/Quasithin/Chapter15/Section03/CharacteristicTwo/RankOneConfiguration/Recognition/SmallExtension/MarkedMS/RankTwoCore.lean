module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoBinary
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Group structure for the small MS block reconstruction

The relative C-component is subnormal and perfect. Subnormality passes the
characteristic-two generalized Fitting condition from LR to L. A simple
central-core marking supplies quasisimplicity of L/O₂(L). Consequently the
remaining shortness obligations concern the whole commutator core and its
module quotient. Shortness transports back to the relative subgroup in LR.

These facts are used by both nonbinary rows in `RankTwoReconstruction`.
Source: Aschbacher--Smith C.1.7 and C.1.31--32, printed pp.123,135--136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- Characteristic two descends to the literal subnormal component. -/
theorem SmallMSPair.component_fitting (h : SmallMSPair κ L R) :
    generalizedFitting L = pCore 2 L := by
  let K := L.subgroupOf (L ⊔ R)
  have hK : generalizedFitting K = pCore 2 K := by
    apply le_antisymm _ ((pCore_le_fitting K 2).trans (fitting_le_generalizedFitting K))
    rw [pCore_subnormal_eq_comap 2 h.component.subnormal]
    apply map_le_iff_le_comap.mp
    rw [← h.fitting]
    exact generalizedFitting_map_subtype_le_of_isSubnormal K h.component.subnormal
  let e : K ≃* L := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
  rw [map_generalizedFitting_equiv, pCore_map_iso, hK]

/-- The perfect component has no nontrivial two-group quotient. -/
theorem SmallMSPair.component_twoPerfect (h : SmallMSPair κ L R) :
    IsPPerfect 2 L := by
  let := h.component_perfect
  intro N hn hq
  let := hn
  have hs : Subsingleton (L ⧸ N) := by
    by_contra! hnt
    exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hq.isNilpotent
  apply eq_top_iff.mpr
  intro l _
  exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)

omit [Finite G] in
/-- A simple central-core quotient and component perfectness give the
quasisimplicity clause of shortness. -/
theorem SmallMSPair.core_quasisimple_of_centralCore
    (h : SmallMSPair κ L R) {A : Type*} [Group A] [IsSimpleGroup A]
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* A) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let := h.component_perfect
  exact { toIsPerfect := inferInstance
          simple := ((centralPreimageQuotientEquiv (pCore 2 L)).symm.trans e).isSimpleGroup }

/-- Only the whole-core module clauses remain after the group structure
and the central-core marking have been established. -/
theorem SmallMSPair.short_of_core (h : SmallMSPair κ L R)
    (he : IsElementaryAbelian 2 (blockU L))
    (hc : blockU L ≤ centralizer (pCore 2 L : Set L))
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hi : BlockModuleIrreducible L) :
    IsShort L :=
  ⟨inferInstance, h.component_twoPerfect, h.component_fitting, he, hc, Or.inl hq, hi⟩

/-- Shortness on the original carrier gives a block inside the literal LR. -/
theorem SmallMSPair.block_of_short (h : SmallMSPair κ L R) (hs : IsShort L) :
    IsBlock (L.subgroupOf (L ⊔ R)) :=
  ⟨inferInstance, hs.of_mulEquiv
    (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm, h.component.subnormal⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
