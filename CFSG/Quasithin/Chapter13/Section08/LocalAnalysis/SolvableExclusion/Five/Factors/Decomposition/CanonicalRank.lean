module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Counting the canonical order-five factors

Distinct order-five factors from D.2.12 and their actual supports are
independent. The product of any finite family embeds by multiplication
into each subgroup containing that family. Its order is 5^s and its
exponent divides five, so the containing group's five-rank is at least s.
This gives s ≤ 2 from the source rank hypothesis, without assuming any
small-order description of P.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.12,
printed pp.183–184, and the five-primary paragraph of 13.8.13, p.951.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open ChapterD
variable {K W : Type*} [Group K] [Group W] [MulDistribMulAction K W]
variable [Finite K] [Finite W] [IsElementaryAbelian 2 W] [FaithfulSMul K W]

theorem canonicalFive_count_le_subgroup_rank {ι : Type*} [Fintype ι]
    (X : ι → Subgroup K) (hX : ∀ i, X i ∈ smallSupportFactors K W 2)
    (hinj : Function.Injective X) (R : Subgroup K) (hXR : ∀ i, X i ≤ R) :
    Fintype.card ι ≤ primeRank 5 R := by
  classical
  let f : ι → smallSupportFactors K W 2 := fun i => ⟨X i, hX i⟩
  have hf : Function.Injective f := fun i j he => hinj (congrArg Subtype.val he)
  have hd := smallSupport_decomposition (G := K) (V := W) (k := 2) (Or.inr rfl)
  have hi : iSupIndep X := hd.1.comp hf
  have hc : Pairwise fun i j => ∀ x y : K, x ∈ X i → y ∈ X j → Commute x y := by
    intro i j hij
    exact hd.2.1 (fun he => hij (hf he))
  let (i : ι) : IsCyclic (X i) := smallSupportFactor_isCyclic (Or.inr rfl) (hX i)
  let (i : ι) : CommGroup (X i) := IsCyclic.commGroup
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : ∀ x : (∀ i, X i), x ^ 5 = 1 := by
    intro x
    funext i
    have hcard : Nat.card (X i) = 5 := (hX i).2.1
    simpa only [Pi.pow_apply, Pi.one_apply, hcard] using pow_card_eq_one' (x := x i)
  have hcard : Nat.card (∀ i, X i) = 5 ^ Fintype.card ι := by
    rw [Nat.card_pi]
    simp only [show ∀ i, Nat.card (X i) = 5 from fun i => (hX i).2.1,
      Finset.prod_const, Finset.card_univ]
  let q := noncommPiCoprod hc
  have hq : q.range ≤ R := by
    rw [noncommPiCoprod_range]
    exact iSup_le hXR
  let qR := q.codRestrict R (fun x => hq ⟨x, rfl⟩)
  have hqi : Function.Injective qR := by
    intro x y he
    exact injective_noncommPiCoprod_of_iSupIndep hi (congrArg Subtype.val he)
  exact primeRank_ge_of_elementary_embedding hp hcard qR hqi

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
