module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.SourceReduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Source
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Quasithin.CoprimeRank

/-!
# Odd rank in the actual marked characteristic-normalizer image

The quotient of Ξ_p(L) is noncyclic in both of its source alternatives.
An odd p-group of p-rank at most one is cyclic, so its p-rank is at least
two. This rank survives both two-core quotients and the inclusion into
the residual Y. We retain the literal image B of Y and the original full
Sylow image in N/O₂(N). Properness follows from nonnormality of Ξ_p(L)
in K, before any A.3.12 model or case-ten assertion is available.

These are the inputs for the containing-model exclusions in the proof of
Aschbacher–Smith 1.3.8, printed p.513, using A.3.12, pp.47–48.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 ChapterA.Section03
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

/-- The pre-embedding source data already forces strict containment. -/
theorem SourceData.residual_lt (h : SourceData 𝒦 p r L T C K) :
    normalizerResidual L (radicalCore p L T) < K := by
  apply lt_of_le_of_ne h.contains_Y
  intro he
  apply h.nonnormal_xi
  rw [← he]
  exact xi_normal_in_intermediate p (normalizerResidual_le L _)

/-- The actual residual image has odd-prime rank at least two. Neither
case (10) nor an elementary-kernel identification is used. -/
theorem SourceData.residual_image_rank (h : SourceData 𝒦 p r L T C K) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    2 ≤ primeRank p (quotientImage (normalizerResidual L (radicalCore p L T)) N) := by
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  let X := XiP p L
  let Y := normalizerResidual L (radicalCore p L T)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  have hrX : 2 ≤ primeRank p (XiQuotient X) := by
    by_contra! hsmall
    apply h.xi_shape.not_isCyclic
    apply h.xi_shape.isPGroup.isCyclic_of_odd_of_elementary_card_le ho
    intro E he
    let := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one
      (show primeRank p (XiQuotient X) ≤ 1 by omega) E
  have hrY : 2 ≤ primeRank p Y := by
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup] at hrX
    exact hrX.trans (primeRank_mono p h.contains_xi)
  have hYN : Y ≤ N := h.contains_Y.trans h.component.1
  change 2 ≤ primeRank p ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 _) pCore_isPGroup,
    ← primeRank_equiv p (imageCoreQuotientEquiv (Y.subgroupOf N)),
    primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 _) pCore_isPGroup,
    primeRank_equiv p (subgroupOfEquivOfLe hYN)]
  exact hrY

/-- The literal marked images and full original Sylow satisfy the proper
local-component hypotheses for containing-model inspection. -/
theorem SourceData.marked_image_setup (h : SourceData 𝒦 p r L T C K) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let B := quotientImage (normalizerResidual L (radicalCore p L T)) N
    let D := quotientImage K N
    ∃ S : Sylow 2 (XiQuotient N),
      (S : Subgroup (XiQuotient N)) = quotientImage (T : Subgroup G) N ∧
      B ∈ localCComponents S ∧
      (S : Subgroup (XiQuotient N)) ≤ normalizer (B : Set (XiQuotient N)) ∧
      B < D ∧ ¬ IsQuasisimple (B ⧸ pCore 2 B) ∧
      2 ≤ primeRank p B ∧ D.IsCComponent := by
  let := h.characteristic
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let Y := normalizerResidual L (radicalCore p L T)
  let q := QuotientGroup.mk' (pCore 2 N)
  have hTN : (T : Subgroup G) ≤ N :=
    (t_le_normalizer_radicalCore p L T).trans
      (normalizer_le_normalizer_characteristic_image _ C)
  have hYN : Y ≤ N := h.contains_Y.trans h.component.1
  let S₀ : Sylow 2 N := T.subtype hTN
  let S := S₀.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S₀ := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN, h.local_Y⟩
  have hSY : (S₀ : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono (t_le_normalizer_Y p h.invariant)
  obtain ⟨hstrict, hnonq⟩ := actual_image_strict_and_not_quasisimple
    T hTN h.local_Y h.component.1 h.component.2 h.residual_lt h.nonsimple_Y
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  refine ⟨S, ?_, ?_, ?_, hstrict, hnonq, h.residual_image_rank,
    h.component.2.map_quotient _⟩
  · rfl
  · simpa only [S, Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hYL
  · exact (map_mono (f := q) hSY).trans ((Y.subgroupOf N).le_normalizer_map q)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
