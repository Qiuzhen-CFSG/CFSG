module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.OddCore
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ComponentData

/-!
# Direct source selection of the escaping ordinary component

The literal escaping I has trivial odd core. If F*(I) is not its two-core,
a genuine ordinary component exists; 1.1.5 supplies its exact model and
marked involution action. Minimality gives the original Sylow-orbit generation
and the source seed acts faithfully. This discharges ComponentData from the
original ResidualInput, preserving all actual ambient embeddings.

Source: Aschbacher--Smith, paragraph before 15.2.24, pp.1117--1118,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 OrdinaryComponents
open Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r

/-- The source component selection before 15.2.24, including the normal Sylow orbit and faithful Z-action. -/
theorem ResidualInput.exists_component_data_direct {I : Subgroup G} (hI : MinimalPlaneEscape Mc ⁅V,B⁆ I)
    (hF : generalizedFitting I ≠ pCore 2 I) :
    ∃ (P : Sylow 2 I) (z : G),
      (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆ ∧
      z ∈ centralInvolutions T ∧ z ≠ 1 ∧ Nonempty (ComponentData (T := T) (Mc := Mc) I P z) := by
  obtain ⟨P,hP⟩ := r.sylow_in_escape hI.1
  obtain ⟨z,hz,hzne,_⟩ := r.exists_central_moved_involution_direct
  have ho := r.oddCore_eq_bot_direct hI.1
  obtain ⟨L,hL⟩ := exists_ordinary_component_of_fstar_ne_twoCore ho hF
  have hm := r.lemma115_direct hI.1 P hP hz hzne
  obtain ⟨hmoved,hout,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple
    h.ambient I P Mc z hm L hL
  let L0 := conjugateSpanBy L (P : Subgroup I)
  have hn : L0.Normal := by
    change (conjugateSpanBy L (P : Subgroup I)).Normal
    rw [conjugateSpanBy_eq_iSup_conj]
    exact componentOrbit_normal_of_normal_or_index_two L P
      (hL.normal_or_index_two_of_odd_rank_le_two
        (Chapter3.sqtk_of_mem_H h.ambient hI.1.1).stronglyQuasithin)
  have hgen : L0.map I.subtype ⊔ (Mc ⊓ I) = I := by
    have hJI : L0.map I.subtype ⊔ (Mc ⊓ I) ≤ I := sup_le (map_subtype_le _) inf_le_right
    rcases r.minimal_intermediate_direct hI le_sup_right hJI with he | he
    · exact (hout ((map_mono (le_conjugateSpanBy L (P : Subgroup I))).trans
        (le_sup_left.trans (he.le.trans inf_le_left)))).elim
    · exact he
  have hfaith : centralInvolutions T ⊓ centralizer (L.map I.subtype : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1
    apply False.elim
    apply hout
    rw [← (r.marked_centralizer_of_seed_card (r.escape_index hI.1).1 hx.1 hx1).2]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hx.2 y hy)
  have hcenter := component_center_eq_twoCore hL ho
  have hcenter2 : IsPGroup 2 (center L) := hcenter ▸ pCore_isPGroup
  exact ⟨P,z,hP,hz,hzne,⟨⟨L,hL,hout,hcenter,hcenter2,
    component_oddCore_eq_bot hL ho,hmoved,hmodel,hfaith,hn,hgen⟩⟩⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
