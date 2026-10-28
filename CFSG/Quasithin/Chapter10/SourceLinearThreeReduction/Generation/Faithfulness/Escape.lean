module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelSelection
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Complete

/-!
# An escaping elementary kernel without an A₅ marking

The general kernel-selection theorem uses the intrinsic Hall witness and its
Frattini factorization with the prescribed T. Source 4.4.13(1), applied to the
actual embedding H → G and D.simpleQTKE, then forces its ambient normalizer
outside M. No module coordinates or later Chapter 10 conclusions enter.

Source: Aschbacher--Smith, 4.4.13, printed pp.623--624, as used in
10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source 4.4.13(1) forces escape for the original H-star Hall actor. -/
theorem source_hstar_elementary_hall_escape
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    {p : ℕ} (hp : p.Prime) (A : Subgroup H) (hAe : IsElementaryAbelian p A)
    (hAY : A ≤ d.witness.abelianGroup)
    (hAS : (A.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (A.map H.subtype : Set G)) :
    ¬ normalizer (A.map H.subtype : Set G) ≤ D.maximalLocal := by
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    exact hH.1.1.1 (by simp only [pCoreIn, he, Subgroup.map_bot])
  have hAS' : (A : Set H) * (T.subtype hH.1.1.2 : Set H) =
      (T.subtype hH.1.1.2 : Set H) * (A : Set H) := by
    apply (Set.image_injective.mpr H.subtype_injective)
    rw [Set.image_mul, Set.image_mul]
    change (A.map H.subtype : Set G) *
        (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) =
      (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) * (A.map H.subtype : Set G)
    simpa only [map_subgroupOf_eq_of_le hH.1.1.2, Sylow.coe_coe] using hAS
  have hg := NormalizerEscape.source4413One_knownSimple G D.simpleQTKE H
    inferInstance inferInstance H.subtype H.subtype_injective hcore hlarge
    (T.subtype hH.1.1.2) hP d.witness.abelianGroup d.hall_le d.hall
    p hp A hAe hAY hAS'
  intro hN
  have hNM : normalizer (A : Set H) ≤ D.maximalLocal.subgroupOf H := by
    intro a ha
    exact hN (A.le_normalizer_map H.subtype (mem_map_of_mem H.subtype ha))
  have htop : (⊤ : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    rw [← hg, source_hstar_parabolicMax_eq_overlap D hH hP]
    exact sup_le le_rfl hNM
  exact hH.1.2 (subgroupOf_eq_top.mp (top_unique htop))

/-- A nontrivial intrinsic Hall kernel contains a genuine escaping elementary
odd actor on the original ambient carrier. -/
theorem source_hstar_hall_kernel_escaping_elementary
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal := by
  obtain ⟨p, A, hp, ho, hA, hAe, hAY, hAC, hAS⟩ :=
    source_hall_sectionKernel_elementary hH.1.1.2 hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  exact ⟨p, A.map H.subtype, hp, ho,
    fun hb => hA ((map_eq_bot_iff_of_injective A H.subtype_injective).mp hb),
    IsElementaryAbelian.map H.subtype, map_mono hAY, hAC, hAS,
    source_hstar_elementary_hall_escape D hH hlarge hP d hp A hAe hAY hAS⟩

end CFSG.Quasithin.Chapter10
