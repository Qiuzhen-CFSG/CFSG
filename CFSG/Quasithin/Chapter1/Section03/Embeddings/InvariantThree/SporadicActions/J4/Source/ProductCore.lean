module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.GroupTheory.SolvableSmallThreeCore
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ElementaryClosure
/-!
# A nontrivial two-core in the original J₄ pair product

The source pair makes H=RS a solvable {2,3}-group. Its three-core has order
at most 27, whereas its full Sylow two-subgroup has order 2^21. The intrinsic
small-three-core theorem therefore gives O₂(H)≠1. In particular the canonical
normal closure of Z(S) is elementary; no transfer to an arbitrary maximal
overgroup is used. The final theorem applies the concrete closure catalogue
at the literal matrix Sylow and retains the original odd subgroup R.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; the solvable
Fitting/Burnside-basis argument is proved in `SolvableSmallThreeCore`.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source

/-- The original permuting pair has a nontrivial intrinsic two-core. -/
theorem product_twoCore_ne_bot {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model} (h : PairInput S R) :
    pCore 2 (R ⊔ S.toSubgroup : Subgroup Janko4.Model) ≠ ⊥ := by
  let H := R ⊔ S.toSubgroup
  have hthree : Nat.card (pCore 3 H) ≤ 27 := by
    have hd := (pCore 3 H).card_subgroup_dvd_card
    change Nat.card (pCore 3 H) ∣ Nat.card (R ⊔ S.toSubgroup : Subgroup Janko4.Model) at hd
    rw [EvenRankTwo.product_card h] at hd
    have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      (pCore 3 H) S.toSubgroup pCore_isPGroup S.isPGroup'
    have hdiv := hcop.dvd_of_dvd_mul_right hd
    have hR : Nat.card R ≤ 27 := by
      rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hR
  have h64 : 64 ∣ Nat.card H := by
    change 64 ∣ Nat.card (R ⊔ S.toSubgroup : Subgroup Janko4.Model)
    rw [EvenRankTwo.product_card h, Janko4.OuterReduction.OddIndex.ambient_sylow_card S]
    exact dvd_mul_of_dvd_right (by norm_num : 64 ∣ 2 ^ 21) _
  exact twoCore_ne_bot_of_solvable_small_three_core (EvenRankTwo.product_solvable h)
    (fun p hp hd => EvenRankTwo.product_prime_divisors h hp hd) hthree h64

/-- Apply the actual elementary-closure catalogue to the unchanged source pair. -/
theorem product_elementaryClosure_catalogue
    {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model} (h : PairInput S R)
    (hS : S.toSubgroup = Janko4.OuterReduction.OddIndex.twoSubgroup) :
    (R ⊔ S.toSubgroup) ≤ Janko4.Cardinality.max1Subgroup
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right =
        CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.candidate 1 ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right =
        CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.candidate 2 ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right =
        CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.candidate 3 ∨
      elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right =
        CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.candidate 4 :=
  elementaryClosure_catalogue S (R ⊔ S.toSubgroup) le_sup_right hS
    (product_twoCore_ne_bot h)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
