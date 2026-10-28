module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionSporadic
public import Theory.SpecificGroups.Held.OddSevenRank
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The Held row of the corrected source inspection

The actual inner image retains the prime-rank restriction through faithful
central descent, including all central covers. Held's certified order bound
leaves even source degree or degree three. The former contradicts its concrete
cubic rank; the latter contradicts its concrete seven-rank. Thus the original
normal-quotient action excludes Held without any whole-radical torus movement.
Source: Aschbacher--Smith 4.3.12(2), 4.3.16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The source rank restriction descends to the literal inner image while retaining
all central covers. The original full-quotient center is prime to the torus prime. -/
theorem SecondarySourceData.componentImage_primeRank_le_one_of_outer_two
    (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hout : IsPGroup 2 (MulAut.Outer (SecondarySourceData.componentImage s))) :
    primeRank p (SecondarySourceData.componentImage s) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.quasisimple
  let a := SecondarySourceData.centralQuotientEquiv s
  have hz := SecondarySourceData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd
  have hr := SecondarySourceData.component_primeRank_eq_one_of_outer_two s D h hp ho hd hz
    (hout.of_injective (MulAut.centralQuotientOuter a) (MulAut.centralQuotientOuter_injective a))
  have hq := primeRank_quotient_le_of_coprime p (center (s.component ⧸ pCore 2 s.component)) hz
  rw [primeRank_congr p a] at hq
  exact hq.trans ((primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hr.le)

/-- The actual Held row is excluded: even source degree contradicts cubic rank,
and the only remaining degree three contradicts seven-rank. -/
theorem SecondarySourceData.not_held_inner
    (s : SecondarySourceData c n) (hn : 1<n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : SecondarySourceData.componentImage s ≃* Held.He) : False := by
  have hd := SecondarySourceData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv] at hd
  have hb := hd.trans Held.OddPrimary.card_dvd
  have hn13 : n<13 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hb)
    norm_num at hd2
  have hnE : Even n ∨ n=3 := by
    interval_cases n
    all_goals first | (solve | left; decide) | (solve | right; rfl) | (solve | norm_num at hb)
  have hout : IsPGroup 2 (MulAut.Outer (SecondarySourceData.componentImage s)) :=
    Held.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  rcases hnE with he | rfl
  · have hr := SecondarySourceData.componentImage_primeRank_le_one_of_outer_two s D h
      Nat.prime_three (by decide) ((Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr he) hout
    rw [primeRank_congr 3 e] at hr
    have hl := Held.three_rank_ge_two
    omega
  · have hr := SecondarySourceData.componentImage_primeRank_le_one_of_outer_two s D h
      (by decide : Nat.Prime 7) (by decide) (by decide) hout
    rw [primeRank_congr 7 e] at hr
    have hl := Held.seven_rank_ge_two
    omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
