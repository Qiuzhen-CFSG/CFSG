module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Recognizing the four-group by a cubic automorphism

A nontrivial automorphism whose cube is one excludes the cyclic group of
order four, since its automorphism group has order two. The prime-square
exponent criterion then supplies an actual isomorphism with C₂ × C₂.

The application is the genuine Frobenius action on the Sz(8) universal
kernel in Aschbacher–Smith I.1.3(5), printed p.407, together with the field
calculation in GLS3 section 6.3, printed p.337.
-/

public section

namespace Theory.GroupAction.CardFourCubic

/-- A group of order four with a nontrivial cubic automorphism is E₄. -/
theorem nonempty_mulEquiv_two_prod_of_cubic {W : Type*} [Group W] [Finite W]
    (hW : Nat.card W = 4) (a : MulAut W) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    Nonempty (W ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have hcyc : ¬ IsCyclic W := by
    intro h
    let := h
    have hd := orderOf_dvd_natCard a
    rw [orderOf_eq_prime ha hne, IsCyclic.card_mulAut, hW] at hd
    exact (by decide : ¬ (3 ∣ Nat.totient 4)) hd
  let : IsKleinFour W := ⟨hW,
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hW).mp hcyc⟩
  let : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    ⟨by simp, by simp [Monoid.exponent_prod]⟩
  exact IsKleinFour.nonempty_mulEquiv

end Theory.GroupAction.CardFourCubic

end
