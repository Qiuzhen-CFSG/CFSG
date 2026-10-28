module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Core
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import Theory.GroupTheory.NormalSectionResidualMonolith

/-!
# Faithfulness and normal generation on the original replacement

The unchanged component has simple two-core quotient on the replacement
carrier. Its image in the ambient two-core quotient is simple and
self-centralizing. Thus every normal subgroup escaping the two-core contains
the two-residual. Independently, MS3 makes the central omega orbit faithful,
which supplies the literal edge-centralizer condition.

These arguments retain the entire moved layer and do not require a natural
subgroup or a Sylow radical. Source: MS93 (2.2), (3.2), (3.6) and Section 7,
printed pp.856,863,870--871,932--933.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)

local notation "K" => Subgroup.subgroupOf (L.subgroupOf (L ⊔ R)) d.overgroup

include e hz in
omit [Finite G] in
/-- The original simple quotient survives both subgroup inclusions. -/
theorem replacement_component_quotient_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  let := relative_quotient_simple (R := R) e hz
  let f := subgroupOfEquivOfLe
    (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).isSimpleGroup

include h e hz in
/-- The actual central orbit has exactly the replacement two-core as kernel. -/
theorem replacement_orbit_centralizer :
    centralizer (ChapterC.MSCentralOrbit.omegaOrbit d.radical : Set d.overgroup) =
      pCore 2 d.overgroup := by
  let := h.relative_normal
  let := replacement_component_quotient_simple e hz d
  exact ChapterC.MSCentralOrbit.omegaOrbit_centralizer K d.radical
    (replacement_radical_isPGroup h d) (replacement_radical_ne_bot h d)
    (replacement_core_le_radical h d) (replacement_self_centralizing h d)
    (replacement_product h d) (replacement_characteristic h d)

include h e hz in
/-- MS93's edge-centralizer condition on the literal replacement graph. -/
theorem replacement_edge_centralizer : EdgeCentralizerCondition d.radical :=
  ChapterC.MSCentralOrbit.edgeCentralizerCondition d.radical
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (replacement_orbit_centralizer h e hz d)

include h e hz in
/-- Escaping normal subgroups contain the actual two-residual, including
when the ambient quotient has outer automorphisms. -/
theorem replacement_normal_generation (N : Subgroup d.overgroup) [N.Normal]
    (hN : ¬ N ≤ pCore 2 d.overgroup) : pResidual 2 d.overgroup ≤ N := by
  let := replacement_component_quotient_simple e hz d
  have hK : (K).IsCComponent :=
    h.component.subgroupOf (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  obtain ⟨_, _, hs, _, hc⟩ := ChapterC.MSCentralOrbit.component_image_structure
    K d.radical hK (replacement_radical_isPGroup h d) (replacement_product h d)
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let : IsSimpleGroup ((pResidual 2 d.overgroup).map q) := by
    rw [replacement_residual h d]
    exact hs
  apply pResidual_le_normal_of_not_le_monolithic_kernel 2 q
    (QuotientGroup.mk'_surjective _) ?_ ?_ N ?_
  · rw [show q.ker = pCore 2 d.overgroup from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup
  · simpa only [replacement_residual h d] using hc
  · simpa only [q, QuotientGroup.ker_mk'] using hN

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
