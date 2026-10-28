module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoFourFusion
public import Theory.GroupTheory.PGroup.AbelianOmega
public import ABG.ChapterII.Section1.C4SquareWreathedRecognition
public import Stellmacher.Recognition.NormalFourOddCoreSetup

/-!
# Recognition from fusion of a normal four at order 32

The centralizer of the normal four has order sixteen. Fusion and the unique
central involution exclude its characteristic subgroups of order two, so
it is `C₄ × C₄`. The Sylow center is cyclic, and the intrinsic index-two
extension criterion gives the wreath presentation of height two.

This directly proves the order-32 specialization of the MacWilliams inputs
1.3–1.4 in Janko–Thompson, Math. Z. 113 (1970), p.386, as applied on p.393.
The stronger theorem records that the ambient simplicity and N₂ conditions,
noncommutativity, and uniqueness of the normal four are not needed for this
step once the order, rank, and fusion data are supplied.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalFourOrder32FusionRecognition

/-- Order, central omega, the elementary rank bound, and fusion suffice for
recognition of the height-two wreath group. -/
public theorem isWreathedOfHeight_two_of_fusion
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ABG.IsWreathedOfHeight S 2 := by
  have hC : IsCyclic (center S) :=
    (S.isPGroup'.to_subgroup (center S)).isCyclic_of_card_omega_one_le_two (by omega)
  have hCi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE
  exact ABG.isWreathedOfHeight_two_of_cyclic_center_of_normal_c4_square hS hC
    (centralizer (E : Set S)) (normal_of_index_eq_two hCi)
    (S.centralizer_four_equiv_c4_square hS hZ hrank E hE hfusion)

/-- The order-32 fused-normal-four recognition step with the full hypotheses
of the simple N₂-group application. -/
public theorem isWreathedOfHeight_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hS : Nat.card S = 32) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (_hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ABG.IsWreathedOfHeight S 2 :=
  isWreathedOfHeight_two_of_fusion S hS hZ hrank E hE hfusion

end Stellmacher.Recognition.NormalFourOrder32FusionRecognition
