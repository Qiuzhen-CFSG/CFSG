module
public import Theory.Quasithin.CentralExtensionRankBound
public import Theory.SpecificGroups.SL2.CommutingUnipotents

/-!
# Two commuting SL₂ factors through an odd central quotient

The two upper root groups embed as the additive product of their common
coefficient field, in the centralizer of the first factor's scalar involution.
An odd central quotient of a quasithin group has involution-centralizer rank
at most three, so twice the positive field degree is at most three.
This forces a prime field without asserting quotient quasithinness.

Source: Aschbacher–Smith A.2.15(2) and A.2.17, printed pp.37–39.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace CentralExtension
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] {r e : ℕ} [Fact r.Prime] [CharP F r]

/-- Two actual commuting faithful SL₂ factors in an odd central quotient
force a prime field if the original group is quasithin. -/
public theorem fieldExponent_eq_one_of_commuting_sl2
    (hr : r ≠ 2) (he : 1 ≤ e) (hcard : Nat.card F = r^e)
    (iso : G ⧸ center G ≃* H) (ho : Odd (Nat.card (center G)))
    (hqt : IsQuasithin G) (f g : SL(2,F) →* H)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hc : ∀ a b, Commute (f a) (g b)) : e = 1 := by
  obtain ⟨hz,hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hr f hf
  have hl : 2*e ≤ primeRank r (centralizer ({f (-1)} : Set H)) := by
    apply primeRank_ge_of_elementary_embedding
      (SpecialLinearGroup.CommutingUnipotents.pair_exponent r) _
      (SpecialLinearGroup.CommutingUnipotents.centralizerPair f g hc)
      (SpecialLinearGroup.CommutingUnipotents.centralizerPair_injective f g hc hf hg)
    change Nat.card (F × F) = _
    rw [Nat.card_prod, hcard, ← pow_add]
    congr 1
    omega
  have hu := primeRank_involutionCentralizer_le_three_of_odd_center hr iso ho hqt
    (orderOf_eq_prime hz2 hz)
  omega
end CentralExtension
