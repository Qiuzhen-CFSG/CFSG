module
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Control
public import Theory.GroupTheory.ReducedNormal.OddByTwoImage
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Minimal-parabolic placement from an odd-by-two action

A noncentral reduced module has centralizer kernel inside the unique maximal
overgroup core. If the Sylow Thompson subgroup fixed that module, Thompson
heredity would make its normalizer the whole parabolic. The selected maximal
local subgroup already contains the ambient Thompson normalizer, so the
Baumann-control placement theorem applies. An odd-by-two action supplies the
needed reduced module by taking the two-core fixed space.

Source: the minimal-parabolic step of Aschbacher–Smith, original 14.1.4.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]

theorem source_noncentral_reduced_minimalParabolic_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hP : IsMinimalParabolicOver T H)
    (U : Subgroup H) (hU : IsPReduced 2 U)
    (hne : centralizer (U : Set H) ≠ ⊤) : H ≤ M := by
  let := hU.normal
  let S := T.subtype hH.2
  obtain ⟨B,hTB,hBH⟩ := hP.1.2.exists
  have hi := (intrinsic_minimalParabolic T H B hP hTB hBH).1
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hker : q.ker ≠ ⊤ := by simpa only [q,QuotientGroup.ker_mk'] using hne
  have hC : centralizer (U : Set H) ≤ minimalParabolicCore S hi := by
    simpa only [q,QuotientGroup.ker_mk'] using
      (minimalParabolic_reduced_image S hi q (QuotientGroup.mk'_surjective _)
        hU.quotient_pCore_eq_bot hker).1
  by_contra hout
  apply hout
  apply source_moved_reduced_minimalParabolic_le hG T hempty hM hJ hH hP U hU
  intro hfix
  have hJS : elementaryAbelianMaxJ (S : Subgroup H) ≤ pCore 2 H := by
    rw [← minimalParabolic_sylow_inf_core S hi]
    exact le_inf (sSup_le fun _ hA => hA.1) (hfix.trans hC)
  have he := elementaryAbelianMaxJ_eq_of_intermediate (S : Subgroup H) (pCore 2 H)
    hJS (pCore_isPGroup.le_sylow_of_normal S)
  have hn : normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) = ⊤ := by
    rw [← he]
    apply top_unique
    have hh := normalizer_le_normalizer_elementaryAbelianMaxJ (pCore 2 H)
    rwa [normalizer_eq_top] at hh
  have hmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le hH.2)
  have hnH : H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    have hh := (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
    rw [hn,hmap,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  exact hout (hnH.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)

theorem source_oddByTwo_minimalParabolic_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hP : IsMinimalParabolicOver T H)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (L : Subgroup A) [L.Normal] (hodd : Odd (Nat.card L))
    (hquot : IsPGroup 2 (A ⧸ L)) (hnon : ¬ IsPGroup 2 A) : H ≤ M := by
  obtain ⟨W,_,hW,hC⟩ := exists_reduced_le_of_odd_by_two_image U q hq hker L hodd hquot
  apply source_noncentral_reduced_minimalParabolic_le hG T hempty hM hJ hH hP W hW
  intro he
  have htop : pCore 2 A = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨g,rfl⟩ := hq a
    exact (show g ∈ (pCore 2 A).comap q from hC ▸ (he ▸ (mem_top g)))
  apply hnon
  have hh := pCore_isPGroup (p := 2) (G := A)
  rw [htop] at hh
  exact hh.of_equiv topEquiv
end CFSG.Quasithin.Chapter15.Section01
