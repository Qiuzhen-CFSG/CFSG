module

public import Theory.Mathieu.M12.SmallParabolicPair.ElementaryNormalizerCover
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The unique normal four-group in the marked M₁₂ Sylow subgroup

The exhaustive normal-elementary classification gives a line, the natural
four, or one of two eights. For the eight whose coordinates are private,
its established self-centralization suffices: a self-centralizing normal
four in a group of order 64 would give an automorphism image of order 16,
whereas a four-group has only six automorphisms.

This identifies the actual embedded four, not just its isomorphism type.
Source: Aschbacher–Smith, the sporadic inspection in 15.3.43, printed p.1140.
The underlying marked permutations and elementary classification retain
attribution in `SmallParabolicPair.Seeds` and `ElementaryNormalizerCover`.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair

private theorem normal_four_not_self_centralizing
    (W : Subgroup M12) [IsElementaryAbelian 2 W] (hc : Nat.card W = 4)
    (hWS : W ≤ sylowCandidate) (hn : sylowCandidate ≤ normalizer (W : Set M12)) :
    centralizer (W : Set M12) ≠ W := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour W := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  intro hC
  let f : sylowCandidate →* MulAut W := W.normalizerMonoidHom.comp (inclusion hn)
  have hk : f.ker = W.subgroupOf sylowCandidate := by
    ext x
    change inclusion hn x ∈ W.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    change (x : M12) ∈ centralizer (W : Set M12) ↔ (x : M12) ∈ W
    rw [hC]
  have hkc : Nat.card f.ker = 4 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv, hc]
  have hr : Nat.card f.range ≤ 6 := by
    simpa only [IsKleinFour.card_mulAut] using f.range.card_le_card_group
  have h := f.ker.card_mul_index
  rw [hkc, index_ker, card_sylowCandidate] at h
  omega

/-- The natural four is the only normal elementary subgroup of order four in the marked Sylow subgroup. -/
theorem normal_four_eq_natural
    (W : Subgroup M12) [IsElementaryAbelian 2 W] (hc : Nat.card W = 4)
    (hWS : W ≤ sylowCandidate) (hn : sylowCandidate ≤ normalizer (W : Set M12)) :
    W = natural := by
  have hne : W ≠ ⊥ := by
    intro he
    have := Subgroup.card_eq_one.mpr he
    omega
  rcases EvenLocal.normal_elementary_cases W hWS hne hn with he | he | he | he
  · have := congrArg (fun A : Subgroup M12 => Nat.card A) he
    rw [hc, card_distinguished] at this
    contradiction
  · exact he
  · exact (normal_four_not_self_centralizing W hc hWS hn
      (he ▸ EvenLocal.centralizer_pure)).elim
  · have := congrArg (fun A : Subgroup M12 => Nat.card A) he
    rw [hc, card_elementary] at this
    contradiction

end Sporadic.Mathieu.M12SmallPair
