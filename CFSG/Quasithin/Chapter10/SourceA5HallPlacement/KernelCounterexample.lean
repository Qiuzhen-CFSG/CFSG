module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelSelection
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelModule
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddNormalizerReduction
/-!
# The actual H-star Hall-kernel counterexample

The intrinsic Hall witness, its Frattini factorization, the original separated
coordinates and the earlier-source 4.4.13(1) assertion produce the exact odd
normalizer used in 4.4.3. Every subgroup is retained in the original ambient
group. This is a consumer of the independently proved module and selection
results; 4.4.13(1) and the subsequent component inspection remain independent.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source 4.4.13(1) applies to the actual Hall subgroup and original Sylow. -/
theorem source_a5_hstar_elementary_hall_escape_of_source4413
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2)
      (source_a5_hstar_minimal_parabolic D e hn hH) n)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2)
      (source_a5_hstar_minimal_parabolic D e hn hH) = D.maximalLocal.subgroupOf H)
    {p : ℕ} (hp : p.Prime) (A : Subgroup H) (hAe : IsElementaryAbelian p A)
    (hAY : A ≤ d.witness.abelianGroup)
    (hAS : (A.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (A.map H.subtype : Set G)) :
    ¬ normalizer (A.map H.subtype : Set G) ≤ D.maximalLocal := by
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    exact hH.1.1.1 (by simp only [pCoreIn,he,Subgroup.map_bot])
  have hAS' : (A : Set H) * (T.subtype hH.1.1.2 : Set H) =
      (T.subtype hH.1.1.2 : Set H) * (A : Set H) := by
    apply (Set.image_injective.mpr H.subtype_injective)
    rw [Set.image_mul,Set.image_mul]
    change (A.map H.subtype : Set G) *
        (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) =
      (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) * (A.map H.subtype : Set G)
    simpa only [map_subgroupOf_eq_of_le hH.1.1.2,Sylow.coe_coe] using hAS
  have hg := earlier D.simpleQTKE H inferInstance inferInstance H.subtype
    H.subtype_injective hcore hlarge (T.subtype hH.1.1.2)
      (source_a5_hstar_minimal_parabolic D e hn hH) d.witness.abelianGroup
      d.hall_le d.hall p hp A hAe hAY hAS'
  intro hN
  have hNM : normalizer (A : Set H) ≤ D.maximalLocal.subgroupOf H := by
    intro a ha
    exact hN (A.le_normalizer_map H.subtype (mem_map_of_mem H.subtype ha))
  have htop : (⊤ : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    rw [← hg,hm]
    exact sup_le le_rfl hNM
  exact hH.1.2 (subgroupOf_eq_top.mp (top_unique htop))

/-- A nontrivial kernel in the actual H-star Hall subgroup yields exactly
an escaping elementary odd actor fixing the original orbit section and module. -/
theorem source_a5_hstar_hall_kernel_escaping_elementary
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2)
      (source_a5_hstar_minimal_parabolic D e hn hH) n)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2)
      (source_a5_hstar_minimal_parabolic D e hn hH) = D.maximalLocal.subgroupOf H)
    (hk : d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (B : Subgroup G), p.Prime ∧ Odd p ∧ B ≠ ⊥ ∧
      IsElementaryAbelian p B ∧ B ≤ H ∧ B ≤ sectionCentralizer (localOrbit T L) ∧
      B ≤ centralizer (D.fullModule : Set G) ∧
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) ∧
      ¬ normalizer (B : Set G) ≤ D.maximalLocal := by
  obtain ⟨p,A,hp,ho,hA,hAe,hAY,hAC,hAS⟩ :=
    source_hall_sectionKernel_elementary hH.1.1.2 _ d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  refine ⟨p,A.map H.subtype,hp,ho,
    fun hb => hA ((map_eq_bot_iff_of_injective A H.subtype_injective).mp hb),
    IsElementaryAbelian.map H.subtype,map_subtype_le A,hAC,?_,hAS,?_⟩
  · exact hAC.trans (source_a5_hall_sectionKernel_centralizes_of_bounded_coordinates
      D e hn ht htn hcoords)
  · exact source_a5_hstar_elementary_hall_escape_of_source4413
      D e hn earlier hH hlarge d hm hp A hAe hAY hAS
end CFSG.Quasithin.Chapter10
