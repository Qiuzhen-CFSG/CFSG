module

public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourNormControlDefs
public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourDiagonalMul
public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourDiagonalKernel

/-!
# The unequal cyclic norm-control certificate

The normal, commuting norm-control subgroup is constructed in the definitions
module. Two proved coordinate facts complete the bound: the two
diagonal signs multiply on automorphisms fixing involutions, and an involutive
automorphism with trivial signs belongs to the control subgroup. The signs then
embed every elementary subgroup disjoint from control into a group of order four.

Source: the explicit C_(2^n) × C₄ automorphism calculation in the norm-control
argument associated with MacWilliams (1970), §1.2.
-/

namespace UnequalCyclicFourNormControl

/-- The two coordinate lemmas suffice for the full uniform certificate. -/
public theorem certificate_of_diagonal_lemmas (n : ℕ) (hn : 3 ≤ n)
    (hmul : ∀ f g : involutionFixing n,
      diagonal n hn ((f : MulAut (V n)) * g) = diagonal n hn f * diagonal n hn g)
    (hkernel : ∀ f : involutionFixing n, (f : MulAut (V n))^2 = 1 →
      diagonal n hn f = 1 → (f : MulAut (V n)) ∈ controlSubgroup n) :
    ∃ T : InvolutionNormControl (V n), ∀ B : Subgroup (MulAut (V n)),
      IsElementaryAbelian 2 B →
      (∀ f ∈ B, ∀ x : V n, x^2 = 1 → f x = x) →
      B ⊓ T.subgroup = ⊥ → Nat.card B ≤ 4 := by
  let d : involutionFixing n →* (ZMod 4 × ZMod 4) :=
    { toFun := fun f => diagonal n hn f
      map_one' := diagonal_one n hn
      map_mul' := hmul }
  refine ⟨control n hn, ?_⟩
  intro B hB hfix hdis
  let : IsElementaryAbelian 2 B := hB
  let inclusion : B →* involutionFixing n :=
    { toFun := fun f => ⟨f, hfix f f.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let s := d.toHomUnits.comp inclusion
  have hs : Function.Injective s := by
    apply s.ker_eq_bot_iff.mp
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    apply Subtype.ext
    have he : diagonal n hn (f : MulAut (V n)) = 1 := by
      have h := congrArg (fun u : (ZMod 4 × ZMod 4)ˣ => (u : ZMod 4 × ZMod 4)) hf
      exact h
    have hfT := hkernel (inclusion f)
      (elemPow_eq_one_of_isElementaryAbelian (f : MulAut (V n)) f.property) he
    have hmem : (f : MulAut (V n)) ∈ B ⊓ (control n hn).subgroup := ⟨f.property, hfT⟩
    rw [hdis, Subgroup.mem_bot] at hmem
    exact hmem
  have hc : Nat.card (ZMod 4 × ZMod 4)ˣ = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact (Nat.card_le_card_of_injective s hs).trans_eq hc

/-- Uniform norm control for C_(2^n) × C₄: every elementary automorphism subgroup
fixing involutions and disjoint from control has order at most four. -/
public theorem certificate (n : ℕ) (hn : 3 ≤ n) :
    ∃ T : InvolutionNormControl (V n), ∀ B : Subgroup (MulAut (V n)),
      IsElementaryAbelian 2 B →
      (∀ f ∈ B, ∀ x : V n, x^2 = 1 → f x = x) →
      B ⊓ T.subgroup = ⊥ → Nat.card B ≤ 4 :=
  certificate_of_diagonal_lemmas n hn (diagonal_mul n hn) (diagonal_kernel_mem n hn)

end UnequalCyclicFourNormControl
