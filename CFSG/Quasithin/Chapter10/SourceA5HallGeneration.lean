module
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter10.SourceA5OddOvergroups
public import CFSG.Quasithin.ChapterE.Section02.Structure.ThreeHallGeneration
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Actual Hall and generation data in the nonnormal A₅ source

The original Fundamental Setup and the A₅ quotient control N_G(T) by the
common-normal theorem. Each original H-star overgroup is therefore a
minimal parabolic whose unique maximal subgroup is literally H intersect M.
The complete E.2.2 dispatcher supplies its Cartan subgroup and an escaping
normalizer for every odd-primary subgroup of that same cyclic subgroup.
All maps retain the original H and prescribed Sylow subgroup.

The generation parameter is positive from the original nontrivial binary
module. If the actual odd Hall subgroup is a three-group, its parameter is
at most two. This is the numerical part of 10.2.3; it does not assert the
separate faithful Hall action or its Borel placement.
Source: Aschbacher–Smith, 10.1.2(6), 10.2.3, pp.742,744–745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

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

theorem source_a5_hstar_minimal_parabolic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hNT := source_a5_normalizer_le_of_orbit_intersection_le D e hn
    (T : Subgroup G) le_rfl (T : Subgroup G).le_normalizer inf_le_left
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  exact minimalParabolic_subtype T H
    (Chapter3.HStar.minimalParabolic T hTM hH (Or.inl hNT))

theorem source_a5_hstar_cartan_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    let hP := source_a5_hstar_minimal_parabolic D e hn hH
    ∃ n : ℕ, IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H ∧
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ H ⊓ normalizer (A.map H.subtype : Set G) ≤ D.maximalLocal := by
  let hP := source_a5_hstar_minimal_parabolic D e hn hH
  obtain ⟨n,hg,hb,d,hescape⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP hlarge
  have he := hstar_maximal_eq_overlap D hH hP
  refine ⟨n,hg,hb,d,he,?_⟩
  intro p hp A ho hA hAp hN
  apply hescape p hp A ho hA hAp
  rw [he]
  intro x hx
  exact hN ⟨x.property,A.le_normalizer_map H.subtype (mem_map.mpr ⟨x,hx,rfl⟩)⟩

theorem source_a5_hstar_generation_bound_of_three_hall
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B) : generationParameter H ≤ 2 := by
  let hP := source_a5_hstar_minimal_parabolic D e hn hH
  have he := hstar_maximal_eq_overlap D hH hP
  exact generationParameter_le_two_of_three_hall
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP B
    (he.symm ▸ hBM) (he.symm ▸ hHall) hB

/-- The original Hall actor's placement in L₀T discharges the entire
numerical part of source10.2.3. No three-group, Borel, marked-model, field
exponent, or normalizer-escape hypothesis remains. -/
theorem source_a5_hstar_generation_bound_of_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : generationParameter H ≤ 2 := by
  have hBodd : Odd (Nat.card B) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  have himage := source_a5_hstar_odd_subgroup_isThreeGroup D e hn hH
    (B.map H.subtype) (map_subtype_le B) hBJ
    (by simpa only [card_map_of_injective H.subtype_injective] using hBodd)
  exact source_a5_hstar_generation_bound_of_three_hall D e hn hH B hBM hHall
    (himage.of_equiv (B.equivMapOfInjective H.subtype H.subtype_injective).symm)

/-- The original nontrivial FSU module makes every local Sylow overgroup
have even order, so its genuine KnownSimple generation minimum is positive. -/
theorem source_hstar_generation_positive
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    0 < generationParameter H := by
  let := D.module_elementary
  let : Nontrivial D.moduleSubgroup := (nontrivial_iff_ne_bot _).mpr D.module_ne_bot
  obtain ⟨n,hnpos,hcard⟩ := D.module_elementary.isPGroup.nontrivial_iff_card.mp
    (inferInstance : Nontrivial D.moduleSubgroup)
  have heven : ¬ Odd (Nat.card H) := by
    apply Nat.not_odd_iff_even.mpr
    apply even_iff_two_dvd.mpr
    apply dvd_trans _ (card_dvd_of_le (D.module_le_sylow.trans hH.1.1.2))
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  exact (source_generation_spec_knownSimple
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) heven).1

end CFSG.Quasithin.Chapter10
