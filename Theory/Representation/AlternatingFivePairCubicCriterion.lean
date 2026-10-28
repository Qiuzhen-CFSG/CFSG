module
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# A cubic criterion for an alternating-five pair

An elementary two-group acting faithfully on the automorphisms of `A₅ × A₅`
has rank at most four. In rank three it contains a nontrivial inner action;
in rank four it contains inner actions supported on the two separate factors.
Consequently the displacement bounds six, eight, and twelve prove the strict
cubic inequality required in the moved-pair case of Appendix D.3.5.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Module
namespace Representation.AlternatingFivePairCubicCriterion
open BinaryOffender BinaryOffender.NaturalTensor
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

lemma rank_eq_primeRank (A : Subgroup G) (hA : IsElementaryTwo A) :
    rank A = primeRank 2 A := by
  let := hA.2
  apply le_antisymm
  · have hc := (primeRank_le_iff_elementary_card_le (p := 2) A).mp le_rfl ⊤
      (IsElementaryAbelian.of_injective (p := 2)
        (⊤ : Subgroup A).subtype Subtype.val_injective)
    rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv] at hc
    rw [hA.card_eq_two_pow_rank] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  · exact IsElementaryAbelian.primeRank_le_of_card_le A hA.card_eq_two_pow_rank.le

/-- Three inner-action tests suffice for the strict cubic inequality. -/
theorem strict_bound (ρ : Representation (ZMod 2) G V)
    (κ : G →* MulAut Pair) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hκ : Function.Injective (κ.comp A.subtype))
    (hlow : ∀ a ∈ A, a ≠ 1 → 6 ≤ operatorFixedCodim (ρ a))
    (hinner : ∀ a ∈ A, ∀ r : Pair, r ≠ 1 → r ^ 2 = 1 → κ a = MulAut.conj r →
      8 ≤ operatorFixedCodim (ρ a))
    (hpair : ∀ a ∈ A, ∀ b ∈ A, ∀ r s : Alt,
      r ≠ 1 → s ≠ 1 → r ^ 2 = 1 → s ^ 2 = 1 →
      κ a = MulAut.conj (r, 1) → κ b = MulAut.conj (1, s) → 12 ≤ fixedCodim ρ A) :
    2 * rank A < fixedCodim ρ A := by
  let := hA.2
  have hr := faithful_actor_rank_le_four (κ.comp A.subtype) hκ
  rw [← rank_eq_primeRank A hA] at hr
  by_cases hsmall : rank A ≤ 2
  · obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have hh := (hlow a ha ha1).trans (operatorFixedCodim_le_fixedCodim ρ A ha)
    omega
  by_cases hthree : rank A = 3
  · have hpr : 3 ≤ primeRank 2 A := by rw [← rank_eq_primeRank A hA, hthree]
    obtain ⟨a, _, r, hr1, hr2, he⟩ := faithful_actor_inner (κ.comp A.subtype) hκ hpr
    have hh := (hinner a a.property r hr1 hr2 he).trans
      (operatorFixedCodim_le_fixedCodim ρ A a.property)
    omega
  · have hpr : 4 ≤ primeRank 2 A := by rw [← rank_eq_primeRank A hA]; omega
    obtain ⟨a, b, r, s, hr1, hs1, hr2, hs2, he, hf⟩ :=
      faithful_actor_independent_inner (κ.comp A.subtype) hκ hpr
    have hh := hpair a a.property b b.property r s hr1 hs1 hr2 hs2 he hf
    omega
end Representation.AlternatingFivePairCubicCriterion
