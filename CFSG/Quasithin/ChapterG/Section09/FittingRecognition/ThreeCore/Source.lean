module
public import Theory.GroupTheory.FaithfulThreeGroupRank
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer
import Mathlib.Tactic

/-!
# Source cubic reduction for G.9.4

The covering automizer theorem bounds the elementary actor rank by two.
If the actual three-core has rank at most one, it is cyclic and its
automorphism group has two-part at most two. Nontriviality then gives
the required lower core-rank bound, without assuming universal A.1.5.
The original irreducible action supplies the moved space and even degree.
The final degree-four consumer applies the proved order-nine normalizer
and retains the actual orthogonal action and subgroup index.

Source: Aschbacher--Smith G.9.4, printed pp.354--355. The noncubic branch,
rank-one degree-four branch and degree-six recognition are independent.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- All cubic-core data follow from the original positive-rank Fitting hypotheses. -/
public theorem threeCoreData_from_source
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    ThreeCoreData ρ A m := by
  have hf := faithful_three_core h hc
  have hm2 := actor_rank_le_two_of_faithful_three_core h hf
  have hne := three_core_ne_bot h hm hf
  let : Nontrivial (pCore 3 G) := (pCore 3 G).nontrivial_iff_ne_bot.mpr hne
  have hp : 0 < primeRank 3 (pCore 3 G) := by
    obtain ⟨n, hn, hcard⟩ := (show IsPGroup 3 (pCore 3 G) from pCore_isPGroup).nontrivial_iff_card.mp inferInstance
    by_contra hh
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mp (show primeRank 3 (pCore 3 G) = 0 by omega)
    exact hz (hcard ▸ dvd_pow_self 3 (by omega : n ≠ 0))
  have hr : m ≤ primeRank 3 (pCore 3 G) := by
    by_cases hsmall : primeRank 3 (pCore 3 G) ≤ 1
    · have ha := Theory.GroupTheory.faithful_two_actor_rank_le_one_of_three_rank_le_one
        A (pCore 3 G) pCore_isPGroup h.card_actor hf hsmall
      omega
    · omega
  exact { faithful := hf
          actor_rank_le := hm2
          core_rank_ge := hr
          moved_eq_top := three_core_moved_eq_top h hm hf
          even_degree := even_degree_of_faithful_three_core h hm hf }

/-- The cubic source input leaves exactly the stated degree and actor-rank cases. -/
public theorem source_cubic_degree_cases
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    CaseOne ρ m ∨
    (m = 1 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 6) :=
  caseOne_or_remaining_degrees h hm (threeCoreData_from_source h hm hc)

/-- The rank-two degree-four cubic source branch has its marked orthogonal action. -/
public theorem source_cubic_rank_two_degree_four
    (h : FittingHypothesis K ρ A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 4) : CaseFour ρ 2 := by
  have data := threeCoreData_from_source h (by decide) hc
  obtain ⟨d⟩ := Four.NineNormalizer.orthogonalNormalizerModel ρ h.faithful hd (pCore 3 G)
    (Four.threeCore_card_nine_of_rank_two h.toSetup data hd)
  exact Four.caseFour_of_orthogonalNormalizer h.toSetup data hd d

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
