module

public import Theory.Representation.FourNineInversion

/-!
# Inversion in a faithful four-group action on a small elementary three-group

An elementary three-group of order at most nine has order one, three, or
nine. The first two orders have automorphism group of order at most two,
so a faithful elementary four-group action forces order nine. The existing
four-on-nine inversion theorem then applies to the specified homomorphism.

Source: Aschbacher--Smith A.1.31(3), printed p.27, the three-primary
supercritical Frattini action used in G.9.4.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation

/-- Faithfulness forces a small elementary three-group to have order nine,
so the specified four-group action contains inversion. -/
theorem exists_inversion_of_elementary_card_four_card_le_nine
    {A W : Type*} [Group A] [Group W] [Finite A] [Finite W]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 W]
    (action : A →* MulAut W) (hfaith : Function.Injective action)
    (hA : Nat.card A = 4) (hW : Nat.card W ≤ 9) :
    ∃ a : A, a ≠ 1 ∧ ∀ w : W, action a w = w⁻¹ := by
  have hcard : Nat.card W = 9 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 W).exists_card_eq
    have hnle : n ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
      simpa only [← hn] using hW
    interval_cases n
    · norm_num at hn
      let : Subsingleton W := (Nat.card_eq_one_iff_unique.mp hn).1
      let : Subsingleton (MulAut W) := ⟨fun x y => MulEquiv.ext (fun z => Subsingleton.elim _ _)⟩
      have hle := Nat.card_le_card_of_injective action hfaith
      norm_num [hA] at hle
    · norm_num at hn
      let : IsCyclic W := isCyclic_of_prime_card hn
      have haut : Nat.card (MulAut W) = 2 := by
        rw [IsCyclic.card_mulAut, hn, Nat.totient_prime]
        decide
      have hle := Nat.card_le_card_of_injective action hfaith
      omega
    · norm_num at hn
      exact hn
  let : MulDistribMulAction A W := MulDistribMulAction.compHom W action
  have hfix : fixingSubgroup A (Set.univ : Set W) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    change a = 1
    apply hfaith
    ext w
    have hw := (mem_fixingSubgroup_iff (M := A)).mp ha w (Set.mem_univ w)
    change action a w = w at hw
    simpa only [map_one, MulAut.one_apply] using hw
  exact exists_inversion_of_elementary_card_four_card_nine hA hcard hfix
end Representation

