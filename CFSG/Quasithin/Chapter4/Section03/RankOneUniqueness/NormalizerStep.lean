module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Setup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Quotient
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.LocalSylow
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.BlockSylow
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
/-!
# The local Sylow stage of original 4.3.1 for every binary PSL₂ quotient

The actual L–Sylow join has characteristic two, residual L, and a unique
maximal subgroup over its Sylow. Its C.5.1–2 counterexample would contradict
C.5.6(6): the literal quotient L/O₂(L) has three-rank at most one. The next
module supplies the finite normalizer induction that makes the local Sylow
Sylow in the full normalizer.

Source: Aschbacher–Smith 4.3.1, printed p.613; proof adapted from the checked
A₅ specialization in Chapter4/Section03/A5/NormalizerStep.lean.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))

private theorem unique_intrinsic {A S : Subgroup G}
    (P : Sylow 2 A) (hP : (P : Subgroup A).map A.subtype = S)
    (hu : Order.HasUniqueMaximalOver S A) :
    Order.HasUniqueMaximalOver (P : Subgroup A) ⊤ := by
  obtain ⟨B,hB,_⟩ := hu.2
  have hBA : B ≤ A := hB.2.le
  have hPB : (P : Subgroup A) ≤ B.subgroupOf A := by
    intro a ha
    exact hB.1 (hP ▸ mem_map_of_mem A.subtype ha)
  have hne : B.subgroupOf A ≠ ⊤ := by
    intro he
    have hh := congrArg (map A.subtype) he
    rw [map_subgroupOf_eq_of_le hBA,← MonoidHom.range_eq_map,A.range_subtype] at hh
    exact hB.2.ne hh
  have hp (D : Subgroup A) (hPD : (P : Subgroup A) ≤ D) (hD : D ≠ ⊤) :
      D ≤ B.subgroupOf A := by
    apply map_le_iff_le_comap.mp
    apply hu.le_maximal hB (hP ▸ map_mono hPD)
    apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hD
    apply map_injective A.subtype_injective
    simpa only [← MonoidHom.range_eq_map,A.range_subtype] using he
  have hco : IsCoatom (B.subgroupOf A) := by
    refine ⟨hne,?_⟩
    intro D hBD
    by_contra hD
    exact hBD.not_ge (hp D (hPB.trans hBD.le) hD)
  refine ⟨hPB.trans_lt (lt_top_iff_ne_top.mpr hne), B.subgroupOf A,
    ⟨hPB,hco.covBy_top⟩,?_⟩
  intro D hD
  apply le_antisymm (hp D hD.1 hD.2.ne)
  exact le_of_eq ((hD.2.eq_or_eq (hp D hD.1 hD.2.ne) le_top).resolve_right hne)

include hpsl

/-- The C.5.6(6) contradiction uses the actual rank-one residual. -/
theorem source_C56_impossible {H M R S : Subgroup G}
    (c : ChapterC.Section05.BlockAnalysis.OriginalHypotheses H M L R S)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (P : Sylow 2 M) (hP : (P : Subgroup M).map M.subtype = S) : False := by
  have hr : primeRank 3 H ≤ 1 := by
    rw [← ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
    have he : (pResidual 2 H) ≃* L :=
      (equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr c.residual)
    rw [primeRank_congr 3 he]
    exact odd_primeRank_le_one hpsl (by decide)
  exact c.false_of_localSylow_threeRank_one hH hr P hP

include D h

/-- The final local-Sylow stage of 4.3.1 on the original rank-one L. -/
theorem normalizer_le_of_source_sylow
    (R : Subgroup G) (hR : IsPGroup 2 R) (hRM : R ≤ normalizer (L : Set G))
    (Q : Sylow 2 L) (hQ : (Q : Subgroup L).map L.subtype ≤ R)
    (P : Sylow 2 (normalizer (R : Set G)))
    (hPM : (P : Subgroup (normalizer (R : Set G))).map
      (normalizer (R : Set G)).subtype ≤ normalizer (L : Set G))
    (hunique : Chapter4.UniqueMaximalOvergroup
      (L ⊔ (P : Subgroup (normalizer (R : Set G))).map
        (normalizer (R : Set G)).subtype) (normalizer (L : Set G))) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let M₀ := normalizer (R : Set G)
  let S := (P : Subgroup M₀).map M₀.subtype
  let H := L ⊔ S
  have hS : IsPGroup 2 S := P.isPGroup'.map M₀.subtype
  have hRS : R ≤ S := by
    let : (R.subgroupOf M₀).Normal :=
      (normal_subgroupOf_iff_le_normalizer R.le_normalizer).mpr le_rfl
    have hpR : IsPGroup 2 (R.subgroupOf M₀) := hR.comap_subtype
    have hh := map_mono (f := M₀.subtype) (hpR.le_sylow_of_normal P)
    rwa [map_subgroupOf_eq_of_le R.le_normalizer] at hh
  obtain ⟨P₀,hP₀⟩ := ChapterC.Section05.CounterexampleCharacteristic.chiZeroBlock_extension_sylow
    L S hS hPM Q (hQ.trans hRS)
  have hu := hasUniqueMaximalOver_map_subtype (sylow_hasUniqueMaximalOver hpsl Q)
  rw [← ChapterC.Section05.CounterexampleCharacteristic.sylow_block_intersection
    L S hS Q (hQ.trans hRS)] at hu
  have hu := hasUniqueMaximalOver_sup_of_normalizes hPM hu
  obtain ⟨P₁,hP₁⟩ := ChapterC.Section05.CounterexampleCharacteristic.chiZeroBlock_extension_sylow
    L R hR hRM Q hQ
  have hr : ∃ Z : Sylow 2 (R ⊔ L : Subgroup G),
      (Z : Subgroup (R ⊔ L : Subgroup G)).map (R ⊔ L).subtype = R := by
    rw [sup_comm R L]
    exact ⟨P₁,hP₁⟩
  obtain ⟨Z,hZ⟩ := hr
  have hf : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 L S
        (by rw [←h.maximal_faithful.2.1.2.2]; exact centralizer_generalizedFitting_le L) hS hPM)
  have hHM : H ≤ normalizer (L : Set G) := sup_le L.le_normalizer hPM
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHM)).mp
      ((h.simpleQTKE.twoLocal_sqtk (unique_sylow_join D h).1.1).subgroup
        (H.subgroupOf (normalizer (L : Set G))))
  let c : ChapterC.Section05.BlockAnalysis.OriginalHypotheses H M₀ L R S := {
    fitting := hf
    sylow := P₀
    sylow_image := hP₀
    unique := unique_intrinsic P₀ hP₀ hu
    residual := embedded_pResidual_join_pGroup L S h.maximal_faithful.2.1.2.1 hS hPM
    R_le := hRS
    T_le := map_subtype_le _
    R_normal := le_rfl
    residual_sylow := Z
    residual_sylow_image := hZ
    no_common_normal := by
      intro N hNR hn
      by_contra hne
      have hNG : M₀ ⊔ H ≤ normalizer (N : Set G) :=
        (normal_subgroupOf_iff_le_normalizer
          (hNR.trans (R.le_normalizer.trans le_sup_left))).mp hn
      have hb := normalizer_le_of_unique_maximalTwoLocal hunique.2.2 (hR.to_le hNR)
        hne (le_sup_right.trans hNG)
      exact hout (le_sup_left.trans (hNG.trans hb)) }
  exact source_C56_impossible hpsl c hH P rfl

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
