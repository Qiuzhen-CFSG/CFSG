module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.InitialMSOrbit
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.CenterBounds

/-!
# The source classification on the initial MS module

The faithful central-omega actor has a normal quasisimple component and a
two-group quotient. The full A.2 theorem passes SQTK to this actual component
section. The complete B.5.1 source theorem then classifies the module on its
literal offender subgroup, including all fixed layers and nonsplit cases.

Source: Meierfrankenfeld–Stellmacher (1993), (2.2), (3.2); Aschbacher–Smith B.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension ChapterC
open MSCentralOrbit G2Holomorph
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

include s

/-- The complete B.5.1 source classification applies to the actual initial
central-omega action, with every premise derived from the original source pair. -/
theorem source_ms_centralOmega_classification :
    let X := omegaCenterIn (pCore 2 I)
    let q := QuotientGroup.mk' (centralizer (X : Set I))
    let B := (c.L.subgroupOf I).map q
    let ρ := NormalElementaryQuotient.representation X q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    B ≤ offenderSubgroup ρ ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (offenderSubgroup ρ).subtype) (B.subgroupOf (offenderSubgroup ρ))) := by
  dsimp only
  let K := c.L.subgroupOf I
  let R := d.S.subgroupOf I
  let X := omegaCenterIn (pCore 2 I)
  let q := QuotientGroup.mk' (centralizer (X : Set I))
  let B := K.map q
  let ρ := NormalElementaryQuotient.representation X q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hstruct := source_ms_centralOmega_actor_structure s
  let : K.Normal := s.normal
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let : IsQuasisimple B := hstruct.1.2
  have hsup : K ⊔ R = ⊤ := by
    rw [← subgroupOf_sup (component_le c)
      ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]
  have hsupq : B ⊔ R.map q = ⊤ := by
    rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq]
  have hquot : IsPGroup 2 ((I ⧸ centralizer (X : Set I)) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (R.map q) ((edge_two_group s).map q) hsupq
  have hsq : IsSQTK KnownSimple.IsKnownSimple B := by
    apply ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) s.sqtk
    exact (ChapterA.Section02.IsSectionOf.subgroup B).ambient_surjective q hq
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion ρ B
    hquot hstruct.2.2 hsq (NormalElementaryQuotient.representation_injective _ _ _ _)
    (source_ms_centralOmega_isFFModule s)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
