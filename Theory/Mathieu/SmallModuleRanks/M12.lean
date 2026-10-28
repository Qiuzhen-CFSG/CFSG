module

public import Theory.Mathieu.SmallModuleRanks.CommutingCover
public import Theory.Mathieu.SmallModuleRanks.M12Certificate
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Intrinsic two-rank of M₁₂

The eight-part noncommuting cover bounds elementary subgroups of the
literal order-64 Sylow subgroup by eight. The elementary-cardinality
criterion and Sylow conjugacy give the native group bound, for the
repository's abelian-generator convention for prime rank.

Source: Aschbacher--Smith, G.7.3(2), printed p.348; rank references p.347.
-/

public section
namespace Sporadic.Mathieu
open M12SmallPair M12SmallPair.SylowAutomorphismGroup
open SmallModuleRanks SmallModuleRanks.M12Certificate

/-- Every elementary subgroup of the marked M₁₂ Sylow group has order at most eight. -/
theorem m12_sylow_elementary_card_le_eight (E : Subgroup sylowCandidate)
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 8 := by
  apply elementary_card_le_of_commuting_cover (fun c a => element (bucket c a)) ?_ ?_ E hE
  · intro g hg
    obtain ⟨i, rfl⟩ := element_surjective g
    have hs : multiply i i = 0 := element_injective (by
      rw [element_multiply, element_zero, ← pow_two]
      exact hg)
    exact ⟨(slot i).1, (slot i).2, congrArg element (square_cover i hs)⟩
  · intro c a b hab
    apply congrArg element
    apply commuting_unique
    apply element_injective
    simpa only [element_multiply] using hab

/-- The native simple M₁₂ has two-rank at most three. -/
theorem m12_twoRank_le_three : primeRank 2 M12 ≤ 3 := by
  rw [commonSylow.primeRank_eq]
  change primeRank 2 sylowCandidate ≤ 3
  apply (primeRank_le_iff_elementary_card_le _).mpr
  exact m12_sylow_elementary_card_le_eight

end Sporadic.Mathieu
