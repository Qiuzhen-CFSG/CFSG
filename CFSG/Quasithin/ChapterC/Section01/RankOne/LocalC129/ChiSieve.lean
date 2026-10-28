module
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Alternating.PrimeRank
public import Theory.Quasithin.CoprimeRank
public import Theory.SpecificGroups.Alternating.SevenComponent.Normality

/-!
# The alternating degrees in a strongly quasithin χ-block

The odd prime rank survives quotienting by the two-core. Hence the actual
alternating quotient has three-rank n/3 at most two. For odd n≥3 this leaves
3, 5 and 7, giving precisely the χ₀ types and the ordinary A₇ block occurring
in the proof of Aschbacher–Smith C.1.29, printed p.134.
-/
public section
namespace CFSG.Quasithin.ChapterC.LocalC129
open Subgroup Theory.GroupTheory
variable {G L : Type*} [Group G] [Finite G] [Group L] [Finite L]

theorem alternating_degree_le_eight {n : ℕ}
    (hs : IsStronglyQuasithin L) (h : IsAlternatingBlock L n) : n ≤ 8 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have hr : primeRank 3 (alternatingGroup (Fin n)) ≤ 2 := by
    rw [← primeRank_congr 3 e, primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 L) pCore_isPGroup]
    exact hs 3 (by decide) (by decide)
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n 3 (by decide) (by decide)] at hr
  omega

theorem chi_zero_or_alternating_seven
    (hs : IsStronglyQuasithin L) (h : IsChiBlock L) :
    IsChiZeroBlock L ∨ IsAlternatingBlock L 7 := by
  rcases h with h | ⟨n, hn, h⟩
  · exact Or.inl (Or.inl h)
  · have hb := alternating_degree_le_eight hs h
    have hlow := h.1
    obtain ⟨k, hk⟩ := hn
    have he : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases he with rfl | rfl | rfl
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr h

theorem chi_zero_or_alternating_seven_in
    (hs : IsStronglyQuasithin G) {K : Subgroup G} (h : IsChiBlockIn K) :
    IsChiZeroBlockIn K ∨ IsBlock K ∧ IsAlternatingBlock K 7 := by
  rcases chi_zero_or_alternating_seven (hs.subgroup K) h.2 with hz | h7
  · exact Or.inl ⟨h.1, hz⟩
  · exact Or.inr ⟨h.1, h7⟩

/-- The ordinary A₇ alternative in the actual ambient group is normal. -/
theorem alternating_seven_normal
    (hs : IsStronglyQuasithin G) {K : Subgroup G}
    (hb : IsBlock K) (ha : IsAlternatingBlock K 7) : K.Normal := by
  obtain ⟨e⟩ := ha.2.2.quotient_iso
  exact alternatingGroup.SevenComponent.normal_of_twoPerfect_core_quotient
    hb.subnormal hb.short.twoPerfect e (hs 3 (by decide) (by decide))
end CFSG.Quasithin.ChapterC.LocalC129
