module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction.ElementaryEight
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction

/-!
# The elementary-eight calculation on the source invariant flag

The cardinalities and incidence come directly from the original invariant
flag. The finite calculation therefore supplies every automorphism premise
of `naturalFlagData_of_automorphism_calculation`, which performs the ambient
residual, generation and commutator lifting through the original action.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), pp.849,1009.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
namespace ElementaryEight
variable {G : Type*} [Group G] [Finite G]
variable {L V : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]

/-- Recover the four automorphism premises from the actual invariant flag. -/
theorem invariantFlag_calculation (F : Chapter12.Section08.InvariantFlag T V 3) :
    Nat.card (coreQuotient (flagResidual ((F.Vi 1).subgroupOf V))) = 3 ∧
    Nat.card (coreQuotient (flagResidual ((F.Vi 2).subgroupOf V))) = 3 ∧
    flagResidual ((F.Vi 1).subgroupOf V) ⊔ flagResidual ((F.Vi 2).subgroupOf V) = ⊤ ∧
    flagMovement ((F.Vi 2).subgroupOf V) (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤ := by
  apply calculation
  · simpa only [F.last, show (2 : ℕ) ^ 3 = 8 by decide] using F.card 3 (by decide)
  · rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv, F.card 1 (by decide)]
    decide
  · rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 2)).toEquiv, F.card 2 (by decide)]
    decide
  · exact Subgroup.subgroupOf_mono V (F.monotone (by decide : 1 ≤ 2))

/-- Supply every finite premise of the source flag constructor, for its literal
point and plane. The ambient lifting remains the checked construction in `Action`. -/
theorem naturalFlagData (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    NaturalFlagData F.H T (F.Vi 1) (F.Vi 2) V (F.E g) L (F.Li L 1) (F.Li L 2) := by
  obtain ⟨hc₁, hc₂, hgen, hm⟩ := invariantFlag_calculation F
  exact naturalFlagData_of_automorphism_calculation d F g hg hc₁ hc₂ hgen hm

end ElementaryEight
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
