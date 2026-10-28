module

public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# Two-rank of the outer automorphism group of PSL₃(4)

The proved outer-order bound divides twelve, so the outer group has no
subgroup of order eight and has two-rank at most two. The marked version
keeps the original group in the conclusion and uses its supplied PSL₃
isomorphism only to transport the order. This is the outer-actor bound used
with the PSL₃(4) binary degree gap in the chief-factor argument.

Source: GLS3, Theorem 2.5.12 and §2.7, through the standard linear, field and
graph automorphism calculation in `OuterThreeStructure`.
-/

public noncomputable section
open scoped MatrixGroups

namespace Matrix.PSL3Four

theorem outer_two_rank_le {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) : primeRank 2 (MulAut.Outer PSL(3,F)) ≤ 2 := by
  apply primeRank_le_two_of_cube_not_dvd
  intro h
  exact (by decide : ¬ 2 ^ 3 ∣ 12)
    (h.trans (OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF))

theorem outer_two_rank_le_of_equiv {F G : Type*} [Field F] [Finite F] [Group G]
    (hF : Nat.card F = 4) (e : G ≃* PSL(3,F)) :
    primeRank 2 (MulAut.Outer G) ≤ 2 := by
  let : Finite G := Finite.of_equiv PSL(3,F) e.toEquiv.symm
  apply primeRank_le_two_of_cube_not_dvd
  intro h
  have hc : Nat.card (MulAut.Outer G) ∣ 12 := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF
  exact (by decide : ¬ 2 ^ 3 ∣ 12) (h.trans hc)

end Matrix.PSL3Four
