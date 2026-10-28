module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.DiagramKernel
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Elementary actors outside the diagram kernel require odd degree

The unique nonidentity involution of the cyclic outer quotient is represented
by the f-th power of the exceptional automorphism. In even degree this is a
field automorphism, so every involution preserves the diagram, including every
inner twist. Consequently every elementary subgroup lies in the diagram kernel.
An elementary actor outside it forces f odd.

Only the proved reduction to a cocycle twist is used. Eliminating that cocycle,
or identifying its fixed group, is unnecessary for this parity conclusion.
The result narrows the external E-member construction in the swapping branch.

Source: GLS3, Theorems 2.5.1 and 2.5.12(e), applied to Aschbacher--Smith
E.1.14(1), printed p.214.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- In even degree every automorphism of square one preserves the diagram;
the inner twist is retained rather than assumed to be trivial. -/
theorem preservesDiagram_of_square_eq_one_of_even {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (heven : Even f)
    (a : MulAut (Sp F)) (ha : a ^ 2 = 1) : PreservesDiagram a := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ f from Nat.pow_lt_pow_right (by decide) hf)
  apply (mem_parabolicClassAction_ker_iff hq a).mp
  by_cases hne : a = 1
  · rw [hne]
    exact (parabolicClassAction hq).ker.one_mem
  have hao : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha, hne⟩
  rcases involution_inner_or_twist hF hf
      SemilinearClassification.inner_field_of_preservesDiagram a hao with
    ⟨g, _, rfl⟩ | ⟨g, rfl, _⟩
  · exact (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram g)
  · apply (parabolicClassAction hq).ker.mul_mem
    · exact (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram g)
    · rw [graph_pow_eq_field_of_even heven]
      exact (mem_parabolicClassAction_ker_iff hq _).mpr (field_preservesDiagram _)

/-- This applies to the original extension action, without any faithfulness
or inner-twist normalization premise. -/
theorem elementary_le_diagramKernel_of_even {G : Type*} [Group G]
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (heven : Even f)
    (hq : 2 < Nat.card F) (A : Subgroup G) [IsElementaryAbelian 2 A] :
    A ≤ diagramKernel L e hq := by
  intro a ha
  apply (mem_diagramKernel_iff L e hq a).mpr
  apply preservesDiagram_of_square_eq_one_of_even hF hf heven
  rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := A) a ha, map_one]

/-- The outstanding external-member calculation is needed only in odd degree. -/
theorem odd_of_elementary_not_le_diagramKernel {G : Type*} [Group G]
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (hq : 2 < Nat.card F)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : ¬ A ≤ diagramKernel L e hq) :
    Odd f := by
  rcases Nat.even_or_odd f with he | ho
  · exact (hA (elementary_le_diagramKernel_of_even L e hF hf he hq A)).elim
  · exact ho

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
