module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Basic
public import Theory.SpecificGroups.SymmetricEight.PairFourGroupObstruction

/-!
# Excluding the actual S₈ middle-node extension

The original V₂ maps faithfully to I/C_I(L), retaining order four and
normality relative to the image of M ∩ I. Under a marking of that entire
local image as the full four-pair stabilizer, the intrinsic permutation
obstruction gives a contradiction.

Only the full Sylow extension is marked here. The component intersection
has the even four-pair stabilizer as its image and must not be substituted
for the full local image. Construction of these markings from the binary
linear model and the quotient conditions remains a separate prerequisite.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the
middle-node paragraph of 15.3.43, printed p.1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

/-- No quotient marking of the full local group as the four-pair stabilizer exists. -/
theorem not_middle_eight
    (e : c.toComponentAction.Quotient ≃* Equiv.Perm (Fin 8))
    (hM : (c.toComponentAction.image M).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer) : False := by
  let d := c.toComponentAction
  obtain ⟨⟨f⟩, hVM, hnormal, _⟩ := c.four_group_image
  let W := (d.image V₂).map e.toMonoidHom
  have hc : Nat.card W = 4 :=
    (Nat.card_congr (f.trans (e.subgroupMap (d.image V₂))).toEquiv).symm.trans
      c.plane_two_card
  have hle : W ≤ Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer :=
    hM ▸ map_mono hVM
  have hn : d.image M ≤ normalizer (d.image V₂ : Set d.Quotient) :=
    (normal_subgroupOf_iff_le_normalizer hVM).mp hnormal
  have hnW : Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer ≤
      normalizer (W : Set (Equiv.Perm (Fin 8))) := by
    rw [← hM]
    exact (map_mono hn).trans ((d.image V₂).le_normalizer_map e.toMonoidHom)
  exact Theory.SpecificGroups.SymmetricEight.PairFourGroupObstruction.no_normal_four
    W hc hle hnW
end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection
