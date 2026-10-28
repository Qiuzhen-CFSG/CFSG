module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterClassifiedAction
public import CFSG.Quasithin.Chapter10.SourceA5BaumannThreeFree
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The minimal parabolic on the actual fixed-center quotient

The HStar group is intrinsically minimal parabolic. Every nontrivial reduced
quotient remains minimal parabolic, and its unique maximal subgroup is the
literal image of H intersect M. This permits the G.6.4 model comparison to
use actual full-Sylow overgroups of the marked quotient groups.

The internal Structure import unfolds only the definition of the parabolic
core in the proof of containment in the unique maximal. No internal name
appears in the public contract.
Source: Aschbacher--Smith, 10.2.1 and B.6.8, printed pp.743,113--115.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem hstar_maximal_eq_overlap
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ D.maximalLocal.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : D.maximalLocal.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- The actual quotient and maximal subgroup needed for the G.6.4 comparison. -/
theorem source_a5_HStar_reduced_quotient_parabolic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (U : Subgroup H) (hred : IsPReduced 2 U) (g : H)
    (hg : g ∉ centralizer (U : Set H)) :
    letI := hred.normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    ∃ hP : IsMinimalParabolicOver ((T.subtype hH.1.1.2).mapSurjective
        (QuotientGroup.mk'_surjective (centralizer (U : Set H)))) ⊤,
      centralizer (U : Set H) ≤ D.maximalLocal.subgroupOf H ∧
      minimalParabolicMax _ hP = (D.maximalLocal.subgroupOf H).map q := by
  let := hred.normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let S := T.subtype hH.1.1.2
  have hP := source_a5_HStar_minimal_parabolic D e hn H hH
  have hne : q.ker ≠ ⊤ := by
    rw [QuotientGroup.ker_mk']
    exact fun he => hg (he ▸ mem_top g)
  obtain ⟨hk,hQ⟩ := minimalParabolic_reduced_image S hP q
    (QuotientGroup.mk'_surjective _) hred.quotient_pCore_eq_bot hne
  have hm := hstar_maximal_eq_overlap D hH hP
  refine ⟨hQ,?_,?_⟩
  · rw [←hm]
    exact (show centralizer (U : Set H) ≤ minimalParabolicCore S hP by
      simpa only [q,QuotientGroup.ker_mk'] using hk).trans
      (normalCore_le _)
  · rw [←hm]
    exact (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective _) hk).symm
/-- The literal image of H intersect M has order prime to three. -/
theorem source_a5_HStar_maximal_image_three_free
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {H : Subgroup G}
    (hHN : H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    {Q : Type*} [Group Q] (q : H →* Q) :
    Nat.Coprime 3 (Nat.card ((D.maximalLocal.subgroupOf H).map q)) := by
  have hc := source_a5_maximal_baumann_normalizer_three_free D e hn hout
  have hi : (D.maximalLocal.subgroupOf H).map H.subtype ≤
      D.maximalLocal ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨hy,hHN y.property⟩
  have hh := hc.coprime_dvd_right (card_dvd_of_le hi)
  rw [card_map_of_injective H.subtype_injective] at hh
  exact hh.coprime_dvd_right (card_map_dvd _ q)
end CFSG.Quasithin.Chapter10
