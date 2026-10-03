module

public import Stellmacher.SectionOne.NineCoreSupportDecompositionCounting

/-!
# The intrinsic faithful nine-on-sixteen support decomposition

The two intrinsic order-four fixed supports are complementary. Normality of
the elementary-nine actor makes the ambient group permute these actual
subgroups through its given action, without any assumption on its order.

Source: Stellmacher, *On the 2-local structure of N-groups*, printed p.47,
(9.1)(8).
-/

@[expose] public section

namespace Stellmacher.SectionOne

universe u

theorem nineCore_support_decomposition
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (W : Subgroup K) (hWnormal : W.Normal)
    (hWelementary : IsElementaryAbelian 3 W)
    (hWcard : Nat.card W = 9) (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    ∃ first second : Subgroup V,
      IsCompl first second ∧ Nat.card first = 4 ∧ Nat.card second = 4 ∧
      ∀ element : K,
        (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
         second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
        (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
         second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first) := by
  obtain ⟨first, second, hcompl, hpair⟩ :=
    nineCoreSupportDecomposition_intrinsic_pair W hWelementary hWcard hVcard hfaith
  have hfirst : Nat.card first = 4 := ((hpair first).mpr (Or.inl rfl)).1
  have hsecond : Nat.card second = 4 := ((hpair second).mpr (Or.inr rfl)).1
  have hne : first ≠ second := by
    intro hequal
    have hbot : first = ⊥ := by simpa [← hequal] using hcompl.inf_eq_bot
    simp [hbot] at hfirst
  exact ⟨first, second, hcompl, hfirst, hsecond,
    nineCoreSupportDecomposition_permuted_of_intrinsic_pair W hWnormal first second hne hpair⟩

end Stellmacher.SectionOne

