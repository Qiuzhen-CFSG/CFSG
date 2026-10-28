module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PositiveStar
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
/-!
# The outside-component precursor to13.1.6

If an actual C-component of a two-local overgroup of T lies outside the
common positive-star normalizer, it cannot centralize the original Sylow
omega-center. B.2.14 puts this omega-center in the overgroup's reduced
subgroup. The reduced-commutator bound then forces the component's intrinsic
module to be nonzero, so1.2.6 gives membership in the genuine faithful local
family. Its later maximality and quasisimplicity are not asserted here.
Source: Aschbacher--Smith, the first paragraph of13.1.6, printed p.868.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01
open MainForward Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

theorem component_outside_positive_star_faithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X H Y : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T)
    (hH : H ∈ HOver G (T : Set G)) (hY : Y ∈ cComponentsIn H)
    (hout : ¬ Y ≤ normalizer (X : Set G)) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥ ∧
      Y ∈ faithfulLocalComponents T := by
  have hCZ := (positive_star_centralizer_unique hG h318 T hX).2.1
  have hmove : ⁅omegaOneCenterAmbient (T : Subgroup G),Y⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    exact hout ((commutator_eq_bot_iff_le_centralizer.mp he).trans hCZ)
  have hYL := ((lemma_1_2_6 T hH).1 hY).2
  have htype := (Terminal.local_component_and_orbit_signalizerType T
    (lemma_1_1_4_6 T (hG.evenCharacteristic T)) hYL).1
  refine ⟨hmove,(mem_faithfulLocalComponents_iff T Y).mpr ⟨hYL,htype,?_⟩⟩
  intro hz
  let B := Y.subgroupOf H
  let e : B ≃* Y := subgroupOfEquivOfLe hY.1
  have hm : B.map H.subtype = Y := map_subgroupOf_eq_of_le hY.1
  have hb : intrinsicSignalizerModule B = ⊥ := by
    apply map_injective (f := H.subtype) H.subtype_injective
    rw [← intrinsicSignalizerModule_map_of_injective H.subtype H.subtype_injective,hm,hz,Subgroup.map_bot]
  have hr : ⁅reducedTwoSubgroup H,B⁆ = ⊥ := bot_unique
    ((reduced_commutator_le_intrinsicModule B hY.2.subnormal
      (htype.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective)).trans_eq hb)
  have hc := congrArg (Subgroup.map H.subtype) hr
  rw [map_commutator,hm,Subgroup.map_bot] at hc
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hi := sylow_omegaCenter_le_reduced (T.subtype hTH)
    (mem_He_iff.mp (lemma_1_1_4_6 T (hG.evenCharacteristic T) hH))
  change omegaOneCenterAmbient ((T.subtype hTH) : Subgroup H) ≤ reducedTwoSubgroup H at hi
  have hi := map_mono (f := H.subtype) hi
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hi
  exact hmove (bot_unique ((commutator_mono hi le_rfl).trans_eq hc))
end CFSG.Quasithin.Chapter13.Section01
