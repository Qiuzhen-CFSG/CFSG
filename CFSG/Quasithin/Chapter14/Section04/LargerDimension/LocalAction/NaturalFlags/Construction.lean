module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction.Action
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags.Construction.ElementaryEight

/-!
# Constructing the original natural flag

The orders and incidence of the actual invariant flag supply the hypotheses
of the elementary-eight calculation: cubic residual quotients, generation by
the two marked residuals, and movement of the plane by the point residual.
`Action` lifts these statements through the literal conjugation homomorphism,
including its possibly noncentral two-core kernel. Sylow supplementation
gives the intersection with the point normalizer.

`naturalFlagData_of_invariant_flag` constructs every `NaturalFlagData` clause
from `NaturalThreeAction`, the actual flag, and `g ∈ L`. It imposes no further
finite-model premises. The source family membership, join and index follow
for the literal residuals. The outer source owner retains construction of
the earlier natural action and flag from Hypothesis 14.3.10.

Source: Aschbacher--Smith, 12.8.2, 12.8.13(1) and 14.4.8(1),
printed pp.849,855,1009.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
variable {G : Type*} [Group G] [Finite G]
variable {L V : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]

/-- Construct the literal source data once the marked automorphism calculation
has been proved. These four premises concern only `MulAut V`; their producer
needs only the flag's orders and incidence. -/
theorem naturalFlagData_of_automorphism_calculation
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L)
    (hc₁ : Nat.card (coreQuotient (flagResidual ((F.Vi 1).subgroupOf V))) = 3)
    (hc₂ : Nat.card (coreQuotient (flagResidual ((F.Vi 2).subgroupOf V))) = 3)
    (hgen : flagResidual ((F.Vi 1).subgroupOf V) ⊔
      flagResidual ((F.Vi 2).subgroupOf V) = ⊤)
    (hm : flagMovement ((F.Vi 2).subgroupOf V)
      (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤) :
    NaturalFlagData F.H T (F.Vi 1) (F.Vi 2) V (F.E g) L (F.Li L 1) (F.Li L 2) := by
  refine {
    H_eq_normalizer := rfl
    L₁_three := Li_three d F 1 F.H inf_le_right hc₁
    moved_eq := moved_eq_of_automorphisms d F hm
    moved_card := ?_
    moved_le_E := natural_flag_seed_le_E d F g hg
    V₁_le_moved := F.le_seed 1
    L₂_three := Li_three d F 2 L inf_le_left hc₂
    L₁_le_L := (F.Li_le L 1).trans inf_le_left
    L₂_le_L := (F.Li_le L 2).trans inf_le_left
    generated := generated_of_image d F hgen
    flag_intersection := flag_intersection d F }
  simpa only [F.last, show (2 : ℕ) ^ 3 = 8 by decide] using F.card 3 (by decide)

/-- The four intrinsic automorphism calculations for the actual invariant flag,
using its orders and incidence. -/
theorem invariant_flag_automorphism_calculation
    (F : Chapter12.Section08.InvariantFlag T V 3) :
    Nat.card (coreQuotient (flagResidual ((F.Vi 1).subgroupOf V))) = 3 ∧
    Nat.card (coreQuotient (flagResidual ((F.Vi 2).subgroupOf V))) = 3 ∧
    flagResidual ((F.Vi 1).subgroupOf V) ⊔
      flagResidual ((F.Vi 2).subgroupOf V) = ⊤ ∧
    flagMovement ((F.Vi 2).subgroupOf V)
      (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤ := by
  apply ElementaryEight.calculation
  · simpa only [F.last, show (2 : ℕ) ^ 3 = 8 by decide] using F.card 3 (by decide)
  · rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv,
      F.card 1 (by decide)]
    decide
  · rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 2)).toEquiv,
      F.card 2 (by decide)]
    decide
  · exact Subgroup.subgroupOf_mono V (F.monotone (by decide : 1 ≤ 2))

/-- Construct the original source flag from the genuine natural action and
the literal invariant point--plane flag. -/
theorem naturalFlagData_of_invariant_flag
    (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    NaturalFlagData F.H T (F.Vi 1) (F.Vi 2) V (F.E g) L
      (F.Li L 1) (F.Li L 2) := by
  obtain ⟨hc₁, hc₂, hgen, hm⟩ := invariant_flag_automorphism_calculation F
  exact naturalFlagData_of_automorphism_calculation d F g hg hc₁ hc₂ hgen hm

/-- The original subgroups satisfy the source family, join and index clauses.
The ambient equalities are consequences of transport, with the literal `F.E g`. -/
theorem source_membership_of_automorphism_calculation
    (d : NaturalThreeAction L V T) (F : Chapter12.Section08.InvariantFlag T V 3)
    (g : G) (hg : g ∈ L)
    (hc₁ : Nat.card (coreQuotient (flagResidual ((F.Vi 1).subgroupOf V))) = 3)
    (hc₂ : Nat.card (coreQuotient (flagResidual ((F.Vi 2).subgroupOf V))) = 3)
    (hgen : flagResidual ((F.Vi 1).subgroupOf V) ⊔
      flagResidual ((F.Vi 2).subgroupOf V) = ⊤)
    (hm : flagMovement ((F.Vi 2).subgroupOf V)
      (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤) :
    F.Li L 1 ∈ YFamily F.H (T : Subgroup G) (F.Vi 2) (F.E g) ∧
      localJoin (F.Li L 2) (F.Li L 1) = L ∧
      ((T : Subgroup G).subgroupOf (F.Li L 1 ⊔ (T : Subgroup G))).index = 3 := by
  have hN := naturalFlagData_of_automorphism_calculation d F g hg hc₁ hc₂ hgen hm
  refine ⟨⟨hN.L₁_three, ?_, ?_⟩, ?_, source_index_three T _ hN.L₁_three⟩
  · rw [hN.moved_eq, hN.moved_card]
  · rw [hN.moved_eq]
    exact hN.moved_le_E
  · exact (sup_comm _ _).trans hN.generated

/-- The actual residuals belong to the source family, generate the original
local group, and have the required Sylow index. -/
theorem source_membership_of_invariant_flag
    (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    F.Li L 1 ∈ YFamily F.H (T : Subgroup G) (F.Vi 2) (F.E g) ∧
      localJoin (F.Li L 2) (F.Li L 1) = L ∧
      ((T : Subgroup G).subgroupOf (F.Li L 1 ⊔ (T : Subgroup G))).index = 3 := by
  obtain ⟨hc₁, hc₂, hgen, hm⟩ := invariant_flag_automorphism_calculation F
  exact source_membership_of_automorphism_calculation d F g hg hc₁ hc₂ hgen hm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
