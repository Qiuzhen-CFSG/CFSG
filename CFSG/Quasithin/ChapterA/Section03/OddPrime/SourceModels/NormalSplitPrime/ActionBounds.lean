module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Action

/-!
# Rank and outer action on the literal component model

The p-prime central quotient preserves the component rank, and the actual
ambient action has p-prime kernel and rank at most two. An original outside
order-p element has noninner image. These facts connect the fixed-subfield
calculations to the original split domain in EvenLinear and CubicLie.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H S : Type*} [Group H] [Finite H] [Group S] [Finite S]
variable {K : Subgroup H} [K.Normal] [IsQuasisimple K]
variable {p : ℕ} [Fact p.Prime]

omit [K.Normal] [IsQuasisimple K] in
theorem central_model_rank (hz : Nat.Coprime p (Nat.card (center K)))
    (e : K ⧸ center K ≃* S) : primeRank p S = primeRank p K := by
  rw [← primeRank_congr p e]
  exact (primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])).symm

theorem normalAction_rank_le_two
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hb : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S) :
    primeRank p (normalAction K e).range ≤ 2 := by
  apply (primeRank_le_of_surjective_of_coprime p (normalAction K e).rangeRestrict
    (normalAction K e).rangeRestrict_surjective ?_).trans hb
  rw [MonoidHom.ker_rangeRestrict, normalAction_ker]
  exact centralizer_coprime K hz (by omega) hb

omit [Finite S] in
theorem outside_action_not_inner
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hb : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    normalAction K e a ∉ MulAut.innerSubgroup S := by
  intro hi
  have hd := prime_dvd_of_action_power_inner hz hr hb e a ha haK
    (m := 1) (by simpa only [pow_one] using hi)
  exact (Fact.out : p.Prime).not_dvd_one hd

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
