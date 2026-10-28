module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dimension balance for restriction ratios

If `U + C ≤ D`, codimension of `C` bounds the sum of codimension of `D`
and the dimension contributed by `U` modulo `U ∩ C`. Equality detects
`D = U + C`. Dividing this balance by a sum of positive actor ranks gives
the strict-decrease-or-equality alternative used for restriction of actions.

The proofs use the dimension formula for a sum and positivity of the
denominators. Source: Aschbacher--Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), Lemma D.2.2, pp. 178--179.
These statements do not require a group action or characteristic two.
-/

public section

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The dimension balance underlying restriction to an invariant subspace. -/
theorem quotient_finrank_add_relative_le (U C D : Submodule K V)
    (h : U ⊔ C ≤ D) :
    Module.finrank K (V ⧸ D) +
        (Module.finrank K U - Module.finrank K (U ⊓ C : Submodule K V)) ≤
      Module.finrank K (V ⧸ C) := by
  have hsum := U.finrank_sup_add_finrank_inf_eq C
  have hC := C.finrank_quotient_add_finrank
  have hD := D.finrank_quotient_add_finrank
  have hle := Submodule.finrank_mono h
  have hinf := Submodule.finrank_mono (inf_le_left : U ⊓ C ≤ U)
  omega

/-- Equality in dimension balance is precisely equality of the containing spaces. -/
theorem quotient_finrank_add_relative_eq_iff (U C D : Submodule K V)
    (h : U ⊔ C ≤ D) :
    Module.finrank K (V ⧸ D) +
        (Module.finrank K U - Module.finrank K (U ⊓ C : Submodule K V)) =
        Module.finrank K (V ⧸ C) ↔ U ⊔ C = D := by
  have hsum := U.finrank_sup_add_finrank_inf_eq C
  have hC := C.finrank_quotient_add_finrank
  have hD := D.finrank_quotient_add_finrank
  have hinf := Submodule.finrank_mono (inf_le_left : U ⊓ C ≤ U)
  constructor
  · intro heq
    apply Submodule.eq_of_le_of_finrank_eq h
    omega
  · intro heq
    have := congrArg (fun S : Submodule K V => Module.finrank K S) heq
    omega

end Submodule

namespace LinearActionRatio

/-- If two contributions fill at most the total, either one has smaller ratio,
or both have the total ratio and the dimension bound is an equality. -/
theorem lt_or_lt_or_eq {v d u b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hbalance : d + u ≤ v) :
    u / c < v / (b + c) ∨ d / b < v / (b + c) ∨
      (u / c = v / (b + c) ∧ d / b = v / (b + c) ∧ d + u = v) := by
  by_cases hu : u / c < v / (b + c)
  · exact Or.inl hu
  by_cases hd : d / b < v / (b + c)
  · exact Or.inr (Or.inl hd)
  have hu' := (le_div_iff₀ hc).mp (le_of_not_gt hu)
  have hd' := (le_div_iff₀ hb).mp (le_of_not_gt hd)
  have htotal : v / (b + c) * (b + c) = v :=
    div_mul_cancel₀ _ (ne_of_gt (add_pos hb hc))
  have hueq : u = v / (b + c) * c := by nlinarith
  have hdeq : d = v / (b + c) * b := by nlinarith
  exact Or.inr (Or.inr ⟨(div_eq_iff hc.ne').mpr hueq,
    (div_eq_iff hb.ne').mpr hdeq, by nlinarith⟩)

/-- Minimality of the total ratio against the kernel contribution forces
the quotient contribution to have no larger ratio. -/
theorem quotient_le_of_total_le_kernel {v d u b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbalance : d + u ≤ v)
    (hminimal : v / (b + c) ≤ d / b) :
    u / c ≤ v / (b + c) := by
  rcases lt_or_lt_or_eq hb hc hbalance with h | h | ⟨h, _, _⟩
  · exact h.le
  · exact (not_lt_of_ge hminimal h).elim
  · exact h.le

end LinearActionRatio

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The geometric form of the ratio alternative: if neither contribution has
a smaller ratio, the intermediate fixed space is exactly the sum. The real
numbers `b` and `c` represent the ranks of a kernel and its quotient. -/
theorem restriction_ratio_alternative (U C D : Submodule K V)
    (h : U ⊔ C ≤ D) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (Module.finrank K U - Module.finrank K (U ⊓ C : Submodule K V) : ℕ) / c <
        (Module.finrank K (V ⧸ C) : ℝ) / (b + c) ∨
    (Module.finrank K (V ⧸ D) : ℝ) / b <
        (Module.finrank K (V ⧸ C) : ℝ) / (b + c) ∨
    ((Module.finrank K U - Module.finrank K (U ⊓ C : Submodule K V) : ℕ) / c =
        (Module.finrank K (V ⧸ C) : ℝ) / (b + c) ∧
      (Module.finrank K (V ⧸ D) : ℝ) / b =
        (Module.finrank K (V ⧸ C) : ℝ) / (b + c) ∧ U ⊔ C = D) := by
  have hbalance : (Module.finrank K (V ⧸ D) : ℝ) +
      (Module.finrank K U - Module.finrank K (U ⊓ C : Submodule K V) : ℕ) ≤
      Module.finrank K (V ⧸ C) := by
    exact_mod_cast quotient_finrank_add_relative_le U C D h
  rcases LinearActionRatio.lt_or_lt_or_eq hb hc hbalance with hlt | hlt | ⟨hu, hd, heq⟩
  · exact Or.inl hlt
  · exact Or.inr (Or.inl hlt)
  · refine Or.inr (Or.inr ⟨hu, hd, (quotient_finrank_add_relative_eq_iff U C D h).mp ?_⟩)
    exact_mod_cast heq

end Submodule
