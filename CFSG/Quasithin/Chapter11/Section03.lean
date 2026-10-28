module

public import Theory.Representation.ScalarEquivariantBilinear
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The eigenvalue obstruction to the shadow of L₄(q)

In the last paragraph of the proof of Proposition 11.3.2, a generator of the
Cartan subgroup has eigenvalues `λ²`, `λ`, and `λ⁻¹` on the three commutator
spaces. Bilinearity and equivariance force `λ² * λ = λ⁻¹`, hence `λ = 1` in
characteristic two. This contradicts the order `q - 1`, where `q = 2ⁿ`, `n > 1`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §11.3, printed pp. 770–775 (PDF pp. 787–792).
The section's proof continues onto p. 775, including Lemmas 11.3.8 and 11.3.9.

This module proves the terminal algebraic contradiction. Proposition 11.3.2
itself still requires the local-group reductions, the compatible field
structures of Lemma 11.3.8, and the commutator construction of Lemma 11.3.9.
In particular, the explicit eigenvalue hypotheses here are intermediate inputs,
not replacements for the hypotheses of Proposition 11.3.2.
-/

namespace CFSG.Quasithin.Chapter11.Section03

variable {K A B C : Type*} [Field K] [CharP K 2]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- The final contradiction of §11.3, with the field-size restriction and the
order of the Cartan eigenvalue made explicit. -/
public theorem no_shadow_eigenvalue_configuration
    (c : A →ₗ[K] B →ₗ[K] C)
    (rA : A → A) (rB : B → B) (rC : C → C)
    (heq : ∀ u v, c (rA u) (rB v) = rC (c u v))
    {n : ℕ} (hn : 1 < n) {a : K} (ha : a ≠ 0)
    (horder : orderOf a = 2 ^ n - 1)
    {u : A} {v : B} (hne : c u v ≠ 0)
    (hu : rA u = a ^ 2 • u) (hv : rB v = a • v)
    (hw : rC (c u v) = a⁻¹ • c u v) : False := by
  have hscalar := ScalarEquivariantBilinear.eigenvalue_mul_eq
    c rA rB rC heq hne hu hv hw
  have haone := ScalarEquivariantBilinear.eq_one_of_sq_mul_eq_inv ha hscalar
  have hpow : 4 ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n)
  rw [haone, orderOf_one] at horder
  omega

end CFSG.Quasithin.Chapter11.Section03
