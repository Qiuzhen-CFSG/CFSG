module

public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates

/-!
# Finite certificate for the M₁₂ Sylow automorphism exponent

Write a, b, c for the three marked generators. Their orders, and the orders
of ab, ac, bc, and acc, are respectively 4, 4, 8, 2, 4, 2, and 2.
An automorphism preserves these seven tests. For every triple satisfying
them, substitution in the checked word coordinates has eighth iterate
fixing each of the three generators. This implication is checked in the
kernel, splitting by the first image to bound the computation size.

Only powers of two are used in `powerTest`, so its two equations specify
these element orders. The certificate does not assume that a permitted
triple extends to an automorphism. Its application to actual automorphisms
is proved in the parent module.

Source context: the outer-group inspection on printed p.510 of
Aschbacher–Smith and GLS3, Table 5.3b. The finite calculation uses the
actual marked subgroup and the verified coordinates in `Coordinates`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup
set_option maxRecDepth 1000000

def power : Fin 64 → ℕ → Fin 64
  | _, 0 => 0
  | x, n + 1 => multiply (power x n) x

theorem element_power (x : Fin 64) (n : ℕ) : element (power x n) = element x ^ n := by
  induction n with
  | zero => exact element_zero
  | succ n ih => rw [power, element_multiply, ih, pow_succ]

def powerTest (x : Fin 64) (n : ℕ) : Prop := power x n = 0 ∧ power x (n / 2) ≠ 0
instance (x : Fin 64) (n : ℕ) : Decidable (powerTest x n) := inferInstanceAs (Decidable (_ ∧ _))

def admissible (a b c : Fin 64) : Prop :=
  powerTest a 4 ∧ powerTest b 4 ∧ powerTest c 8 ∧
  powerTest (multiply a b) 2 ∧ powerTest (multiply a c) 4 ∧
  powerTest (multiply b c) 2 ∧ powerTest (multiply (multiply a c) c) 2
instance (a b c : Fin 64) : Decidable (admissible a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

def substituteWord (a b c : Fin 64) : List (Fin 3) → Fin 64
  | [] => 0
  | i :: w => multiply (![a,b,c] i) (substituteWord a b c w)

def substitute (a b c i : Fin 64) : Fin 64 := substituteWord a b c (words i)

def repeatSubstitute (a b c : Fin 64) : ℕ → Fin 64 → Fin 64
  | 0, i => i
  | n+1, i => substitute a b c (repeatSubstitute a b c n i)

set_option maxHeartbeats 2000000 in
theorem eighth_power_check : ∀ a b c : Fin 64, admissible a b c →
    ∀ j : Fin 3, repeatSubstitute a b c 8 ⟨j.val + 1, by omega⟩ = ⟨j.val + 1, by omega⟩ := by
  have check : ∀ a : Fin 64, powerTest a 4 →
      ∀ b : Fin 64, powerTest b 4 → powerTest (multiply a b) 2 →
      ∀ c : Fin 64, powerTest c 8 → powerTest (multiply a c) 4 →
      powerTest (multiply b c) 2 → powerTest (multiply (multiply a c) c) 2 →
      ∀ j : Fin 3, repeatSubstitute a b c 8 ⟨j.val + 1, by omega⟩ =
        ⟨j.val + 1, by omega⟩ := by
    intro a
    fin_cases a <;> decide +kernel
  rintro a b c ⟨ha, hb, hc, hab, hac, hbc, hacc⟩
  exact check a ha b hb hab c hc hac hbc hacc

end Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup
