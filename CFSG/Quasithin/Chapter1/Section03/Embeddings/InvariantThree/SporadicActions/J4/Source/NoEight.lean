module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ProductCore
public import Theory.GroupTheory.ElementaryEightSolvableMinimal

/-!
# Excluding the elementary-eight closure in the original J₄ pair

The canonical closure is minimal normal in the original solvable {2,3}
product, so the intrinsic elementary-eight action theorem excludes order
eight. The exact matrix catalogue then leaves max1 containment or its literal
order-two and order-four rows. No maximal-Sylow-overgroup cover is used.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511. The actual product,
normal closure and certified kernel coordinates are retained throughout.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The source product cannot have an elementary-eight canonical closure. -/
theorem product_elementaryClosure_card_ne_eight
    {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model} (h : PairInput S R) :
    Nat.card (elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right) ≠ 8 := by
  intro he
  let H := R ⊔ S.toSubgroup
  let E := centralClosure S H le_sup_right
  let _ := centralClosure_elementary_of_twoCore_ne_bot S H le_sup_right
    (product_twoCore_ne_bot h)
  have hc : Nat.card E = 8 :=
    (card_map_of_injective H.subtype_injective).symm.trans he
  exact not_minimal_normal_elementary_eight_of_solvable_two_three E hc
    (EvenRankTwo.product_solvable h)
    (fun p hp hd => EvenRankTwo.product_prime_divisors h hp hd) (by
      intro B hBE hBn
      let _ := hBn
      exact centralClosure_minimal S H le_sup_right B hBE)

/-- Only the actual max1, order-two and order-four rows survive for the original pair. -/
theorem product_elementaryClosure_three_cases
    {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model} (h : PairInput S R)
    (hS : S.toSubgroup = Janko4.OuterReduction.OddIndex.twoSubgroup) :
    (R ⊔ S.toSubgroup) ≤ Janko4.Cardinality.max1Subgroup
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right = KernelOrders.candidate 1 ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right = KernelOrders.candidate 2 := by
  rcases product_elementaryClosure_catalogue h hS with hm | h1 | h2 | h3 | h4
  · exact Or.inl hm
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)
  · exfalso
    apply product_elementaryClosure_card_ne_eight h
    rw [h3, KernelOrders.pureKernelCatalogue.2 3]
    rfl
  · exfalso
    apply product_elementaryClosure_card_ne_eight h
    rw [h4, KernelOrders.pureKernelCatalogue.2 4]
    rfl

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
