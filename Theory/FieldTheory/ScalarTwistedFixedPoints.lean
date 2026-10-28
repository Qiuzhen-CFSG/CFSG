module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Ring.Action.End
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Fixed points of scalar-twisted field involutions

A nonzero fixed vector w identifies each solution of c σ(x) = x with a
fixed-field element x/w. If no such nonzero vector exists, the fixed set
is a singleton. Thus scalar twisting cannot increase the fixed-point order.

For a nontrivial field involution the fixed-field theorem gives degree two,
so its order squared equals the original field order. Above order four,
twice the number of scalar-twisted fixed points is strictly less than the
field order. No restriction to odd binary field degrees is involved.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
Proposition 16.5.1, printed p.1194, the outer-action estimate on U_L.
-/

public section

namespace FiniteField
variable {F : Type*} [Field F] [Finite F]

/-- Multiplying a field automorphism by a scalar cannot increase the number
of its additive fixed points. -/
theorem card_scalar_fixed_le (σ : F ≃+* F) (c : F) :
    Nat.card {x : F // c * σ x = x} ≤ Nat.card (FixedBy.subfield F σ) := by
  classical
  by_cases h : ∃ w : F, c * σ w = w ∧ w ≠ 0
  · obtain ⟨w, hw, hw0⟩ := h
    have hc : c ≠ 0 := by
      intro hc
      apply hw0
      simpa [hc] using hw.symm
    let f : {x : F // c * σ x = x} → FixedBy.subfield F σ := fun x =>
      ⟨x.val / w, by
        change σ (x.val / w) = x.val / w
        rw [map_div₀]
        calc
          σ x.val / σ w = (c * σ x.val) / (c * σ w) := (mul_div_mul_left _ _ hc).symm
          _ = x.val / w := by rw [x.property, hw]⟩
    apply Nat.card_le_card_of_injective f
    intro x y he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    exact (div_left_inj' hw0).mp hh
  · push Not at h
    apply Nat.card_le_card_of_injective (fun _ : {x : F // c * σ x = x} =>
      (0 : FixedBy.subfield F σ))
    intro x y _
    exact Subtype.ext ((h x x.property).trans (h y y.property).symm)

/-- A nontrivial involution of a finite field has a fixed field of square-root order. -/
theorem card_involution_fixed_sq (σ : F ≃+* F)
    (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F) :
    Nat.card (FixedBy.subfield F σ) ^ 2 = Nat.card F := by
  let H := Subgroup.zpowers σ
  let K := FixedPoints.subfield H F
  have ho : orderOf σ = 2 := orderOf_eq_prime (by ext x; exact hs x) hne
  have : Finite H := Finite.of_injective
    (fun g : H => (g.val : F → F)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank K F = 2 := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, ho]
  have hK : K = FixedBy.subfield F σ := by
    ext x
    change (∀ g : H, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rw [← hK, ← hd, Module.natCard_eq_pow_finrank (K := K) (V := F)]

/-- Above order four, even a scalar twist of a nontrivial field involution
loses strictly more fixed points than a two-element action image gains. -/
theorem two_mul_card_scalar_fixed_lt (hF : 4 < Nat.card F)
    (σ : F ≃+* F) (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F) (c : F) :
    2 * Nat.card {x : F // c * σ x = x} < Nat.card F := by
  have hle := card_scalar_fixed_le σ c
  have hsq := card_involution_fixed_sq σ hs hne
  have hlarge : 2 < Nat.card (FixedBy.subfield F σ) := by nlinarith
  nlinarith
end FiniteField
