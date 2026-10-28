module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneHeldBounds
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Transport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple

/-!
# Original-action generation comparisons for the two rank-one rows

The actual H-star Hall--Cartan witness maps faithfully through conjugation
on L/O2(L). The completed unitary/Suzuki Hall-faithfulness theorem supplies
its kernel condition, so n(H) is bounded by the Cartan parameter of this
literal quotient-action image. E.3.35 and the original maximal-local guard
then bound min(w,r) by that same parameter, retaining the original Sylow.

These are ambient comparisons with no odd-control or generation callbacks.
The unitary/Suzuki Cartan estimates and the final exclusions remain with
qt-d-1222-nonmathieu-unitary-suzuki-exclusion. In particular, the last Suzuki
application explicitly retains its model Cartan estimate until proved.
Source: Aschbacher--Smith 4.4.14, E.3.35--39 and 7.3.4,
printed pp.624--625,238--240,699.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

include D in
private theorem hstar_generation_le_quotientAction_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hfaith : 1 < generationParameter H →
      ∀ B : Subgroup H, B ≤ (normalizer (L : Set G)).subgroupOf H →
        IsHallSubgroup oddPrimes (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)) →
        B.map H.subtype ⊓ Chapter4.sectionCentralizer L = ⊥) :
    generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range := by
  by_cases hn : generationParameter H ≤ 1
  · exact hn.trans one_le_nPrime
  have hlarge : 1 < generationParameter H := by omega
  let F := D.fundamentalSetup h.toHypothesis1221
  have hFM : F.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [D.localOrbit_eq]
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := hFM.symm ▸ hH
  obtain ⟨hP,f,_,hf,d,he,_,_⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one F hH' hlarge
  have he' : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H := by simpa only [hFM] using he
  have hB := hfaith hlarge d.witness.abelianGroup (d.hall_le.trans_eq he') (he' ▸ d.hall)
  let w := overlapWitness hH.1.1.2 D.sylow_normalizes_component d he'
  apply hf.trans (le_nPrime_quotientAction_of_faithful L w ?_)
  exact (congrArg (fun C : Subgroup G => C ⊓ Chapter4.sectionCentralizer L)
    (overlapWitness_cyclic_image hH.1.1.2 D.sylow_normalizes_component d he')).trans
      (bot_unique ((inf_le_inf_right _ (map_mono d.witness.cyclic_le)).trans_eq hB))

/-- E.3.35 on every actual outside H-star member, with generation attained
by the full known-simple source theorem. -/
theorem sourceOrbit_nonMathieu_min_parameters_le_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤ (generationParameter H : ℕ∞) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  have hu : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) : Subgroup G) : Set G)) =
      {normalizer (L : Set G)} := by
    ext N
    constructor
    · intro hN
      exact Set.mem_singleton_iff.mpr (h61.unique N hN.1 (inf_le_right.trans hN.2))
    · intro hN
      obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨h61.maximalTwoLocal, h61.normalizer_sylowCentralizer_le⟩
  by_contra hn
  apply hH.1.2
  apply SourceContainment.le_of_sqtk_knownSimple D.sourceOrbit_weakClosure_setup
    (T.subtype hH.1.1.2) (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
    hu (inf_le_right.trans h61.centralizer_le) ?_ (lt_of_not_ge hn)
  change (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) ≤
    ((T : Subgroup G).subgroupOf H).map H.subtype
  rw [map_subgroupOf_eq_of_le hH.1.1.2]
  exact inf_le_left

/-- The unitary Hall-faithfulness theorem bounds the actual outside generation. -/
theorem sourceOrbit_unitary_generation_le_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range :=
  D.hstar_generation_le_quotientAction_nPrime h hH
    (fun hlarge B hBM hHall => D.sourceOrbit_unitary_hall_faithful
      h hmany hV hs hnm hnon hs2 hq hH hlarge B hBM hHall)

/-- The Suzuki Hall-faithfulness theorem bounds the actual outside generation. -/
theorem sourceOrbit_suzuki_generation_le_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range :=
  D.hstar_generation_le_quotientAction_nPrime h hH
    (fun hlarge B hBM hHall => D.sourceOrbit_suzuki_hall_faithful
      h hmany hV hs hnm hnon hm e hH hlarge B hBM hHall)

private theorem min_parameters_le_nPrime_of_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hgen : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤
      (nPrime (normalizerPCoreQuotientAction L).range : ℕ∞) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ h61.maximalTwoLocal h61.sylow_le)
  exact (D.sourceOrbit_nonMathieu_min_parameters_le_generation h hmany hV hnon hH).trans
    (ENat.natCast_le_natCast.mpr (hgen H hH))

theorem sourceOrbit_unitary_min_parameters_le_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤
      (nPrime (normalizerPCoreQuotientAction L).range : ℕ∞) :=
  D.min_parameters_le_nPrime_of_generation h hmany hV hnon
    (fun _ hH => D.sourceOrbit_unitary_generation_le_nPrime h hmany hV hs hnm hnon hs2 hq hH)

theorem sourceOrbit_suzuki_min_parameters_le_nPrime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    min (globalW D.sourceOrbit T) (globalR D.sourceOrbit) ≤
      (nPrime (normalizerPCoreQuotientAction L).range : ℕ∞) :=
  D.min_parameters_le_nPrime_of_generation h hmany hV hnon
    (fun _ hH => D.sourceOrbit_suzuki_generation_le_nPrime h hmany hV hs hnm hnon hm e hH)

/-- The upper w-bound from the remaining intrinsic Suzuki Cartan estimate.
Its model premise remains with the final exclusion owner named above. -/
theorem sourceOrbit_suzuki_globalW_le_of_cartan_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hc : nPrime (normalizerPCoreQuotientAction L).range ≤ 2 * m + 1) :
    globalW D.sourceOrbit T ≤ (2 * m + 1 : ℕ) := by
  have hb := (D.sourceOrbit_suzuki_min_parameters_le_nPrime h hmany hV hs hnm hnon hm e).trans
    (ENat.natCast_le_natCast.mpr hc)
  have hr := (D.sourceOrbit_suzuki_initial_parameters h hmany hV hs hnon hm e).1
  have hlt : ((2 * m + 1 : ℕ) : ℕ∞) < globalR D.sourceOrbit :=
    lt_of_lt_of_le (by exact_mod_cast (show 2 * m + 1 < 2 * (2 * m + 1) by omega)) hr
  exact (min_le_iff.mp hb).resolve_right (not_le_of_gt hlt)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
