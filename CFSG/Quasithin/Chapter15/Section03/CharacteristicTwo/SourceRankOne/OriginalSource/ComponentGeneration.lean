module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Holomorph
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ComponentGeneration

/-!
# Conjugate generation in the original small-extension source

The source component is quasisimple modulo its intrinsic two-core and is
normal in its product with the specified Sylow subgroup. These original
hypotheses supply MS93 (2.3)(b) on the literal free holomorph. The component
quotient is transported through the actual subgroup-of equivalence; no
simple quotient, natural module, or faithful component action is assumed.

Source: MS93 (2.3)(b) and (3.8), printed pp.857 and 877; Aschbacher--Smith
C.1.31--32 and 15.3.31, printed pp.135--136 and 1132.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open EightGeometry.NaturalModule.Recognition ChapterC
namespace ComponentGeneration
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

include s

/-- The original source discharges the relative-generation premise of MS93 (2.3). -/
theorem generation : BinaryMS.MS93.CriticalCriterion.Generation (d.S.subgroupOf I) := by
  let := s.normal
  let e := subgroupOfEquivOfLe (component_le c)
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := c.core_quotient_quasisimple
  let : IsQuasisimple ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  apply MSCentralOrbit.component_generation (c.L.subgroupOf I) (d.S.subgroupOf I)
    (LocalData.thompson_component_in c.le_thompson c.component)
    (G2Holomorph.edge_two_group s) _ (G2Holomorph.core_le_edge s)
  rw [←subgroupOf_sup (component_le c)
    ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]

end ComponentGeneration
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
