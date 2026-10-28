module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylow
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NormalizerStep

/-!
# The rank-one normalizer bound under the original Sylow

Suppose `T ∩ L ≤ R ≤ T` and `T` normalizes `R`. Then `N_G(R) ≤ N_G(L)`.
This is the ambient-Sylow case of original 4.3.1: no normalizer induction
is needed because `T` is already Sylow in `G`. The actual join `LT` has
characteristic two, residual `L`, and a unique maximal subgroup over `T`.
A counterexample therefore satisfies C.5.1–2, whereas C.5.6 contradicts
the three-rank bound of the literal binary PSL₂ quotient of `L`.

The input is the original rank-one `Input`; no chosen-module conclusion
or normalizer bound is assumed. The changed-Sylow extension applies this
to `R = N_T(L₂)`, discharging the use of 4.3.17 in original 5.2.2.

Source: Aschbacher–Smith, 4.3.1, p.613, and 5.2.2, p.648.
Proof adapted from `Chapter4/Section03/RankOneUniqueness/NormalizerStep.lean`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
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

/-- The rank-one normalizer bound when the original Sylow normalizes R. -/
theorem Input.normalizer_le_of_sylow_normalizes
    {T : Sylow 2 G} {L W R : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hRT : R ≤ (T : Subgroup G)) (hUR : (T : Subgroup G) ⊓ L ≤ R)
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G)) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  have hL : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.1, ?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hL
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes) (le_componentOrbit L T)
  have hunique := hu.normalizer_unique
  rw [he] at hunique
  let M₀ := normalizer (R : Set G)
  let H₀ := L ⊔ (T : Subgroup G)
  have hR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hRM : R ≤ normalizer (L : Set G) := hRT.trans h.sylow_normalizes
  let P := T.subtype hTR
  have hP : (P : Subgroup M₀).map M₀.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTR
  obtain ⟨Q,hQ'⟩ := exists_sylow_component h.sylow_normalizes
  have hQR : (Q : Subgroup L).map L.subtype ≤ R := hQ'.symm ▸ hUR
  let P₀ := T.subtype (show (T : Subgroup G) ≤ H₀ from le_sup_right)
  have hP₀ : (P₀ : Subgroup H₀).map H₀.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hum := hasUniqueMaximalOver_map_subtype
    (Chapter4.Section03.RankOneUniqueness.sylow_hasUniqueMaximalOver h.linear Q)
  rw [hQ', inf_comm] at hum
  have hum := hasUniqueMaximalOver_sup_of_normalizes h.sylow_normalizes hum
  obtain ⟨P₁,hP₁⟩ := ChapterC.Section05.CounterexampleCharacteristic.chiZeroBlock_extension_sylow
    L R hR hRM Q hQR
  have hr : ∃ Z : Sylow 2 (R ⊔ L : Subgroup G),
      (Z : Subgroup (R ⊔ L : Subgroup G)).map (R ⊔ L).subtype = R := by
    rw [sup_comm R L]
    exact ⟨P₁,hP₁⟩
  obtain ⟨Z,hZ⟩ := hr
  have hf : generalizedFitting H₀ = pCore 2 H₀ :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 L (T : Subgroup G)
        (by rw [← h.local_mem.2.2.2.1]; exact centralizer_generalizedFitting_le L)
        T.isPGroup' h.sylow_normalizes)
  have hHM : H₀ ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
  have hH₀ : IsSQTK KnownSimple.IsKnownSimple H₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup
        (H₀.subgroupOf (normalizer (L : Set G))))
  let c : ChapterC.Section05.BlockAnalysis.OriginalHypotheses H₀ M₀ L R (T : Subgroup G) := {
    fitting := hf
    sylow := P₀
    sylow_image := hP₀
    unique := unique_intrinsic P₀ hP₀ hum
    residual := embedded_pResidual_join_pGroup L (T : Subgroup G)
      h.local_mem.2.2.1 T.isPGroup' h.sylow_normalizes
    R_le := hRT
    T_le := hTR
    R_normal := le_rfl
    residual_sylow := Z
    residual_sylow_image := hZ
    no_common_normal := by
      intro N hNR hn
      by_contra hne
      have hNG : M₀ ⊔ H₀ ≤ normalizer (N : Set G) :=
        (normal_subgroupOf_iff_le_normalizer
          (hNR.trans (R.le_normalizer.trans le_sup_left))).mp hn
      have hb := normalizer_le_of_unique_maximalTwoLocal hunique (hR.to_le hNR)
        hne (le_sup_right.trans hNG)
      exact hout (le_sup_left.trans (hNG.trans hb)) }
  exact Chapter4.Section03.RankOneUniqueness.source_C56_impossible h.linear c hH₀ P hP

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
