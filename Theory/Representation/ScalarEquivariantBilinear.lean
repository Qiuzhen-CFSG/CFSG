module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.Torsion.Field

/-!
# Bilinear pairings from scalar symmetries

A biadditive pairing is bilinear over a field if its symmetries realize every
nonzero scalar on either input and on the output while fixing the other input.
For an equivariant bilinear pairing, the eigenvalue of a nonzero paired vector
is the product of the input eigenvalues.

The proofs first use the symmetries to establish scalar compatibility (handling
zero by additivity), then cancel scalar multiplication on a nonzero vector.
In characteristic two, the identity `a² * a = a⁻¹` forces `a = 1`, by applying
Frobenius twice to `a - 1`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 11.3.9 and the final paragraph of the proof of
Proposition 11.3.2, printed p. 775. These are general linear-algebra facts;
the local-group construction supplying the symmetries is a separate input.
-/

namespace ScalarEquivariantBilinear
variable {K A B C X : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- Scalar symmetries in both variables upgrade a biadditive pairing to a
bilinear map. The indexing type need not carry a group structure. -/
public theorem exists_bilinear_of_scalar_actions
    (c : A →+ B →+ C)
    (rA : X → A → A) (rB : X → B → B) (rC : X → C → C)
    (heq : ∀ x u v, c (rA x u) (rB x v) = rC x (c u v))
    (hleft : ∀ a : K, a ≠ 0 → ∃ x : X,
      (∀ u, rA x u = a • u) ∧ (∀ v, rB x v = v) ∧
      (∀ w, rC x w = a • w))
    (hright : ∀ a : K, a ≠ 0 → ∃ x : X,
      (∀ u, rA x u = u) ∧ (∀ v, rB x v = a • v) ∧
      (∀ w, rC x w = a • w)) :
    ∃ b : A →ₗ[K] B →ₗ[K] C, ∀ u v, b u v = c u v := by
  have hl (a : K) (u : A) (v : B) : c (a • u) v = a • c u v := by
    by_cases ha : a = 0
    · simp [ha]
    · obtain ⟨x, hxA, hxB, hxC⟩ := hleft a ha
      simpa only [hxA, hxB, hxC] using heq x u v
  have hr (a : K) (u : A) (v : B) : c u (a • v) = a • c u v := by
    by_cases ha : a = 0
    · simp [ha]
    · obtain ⟨x, hxA, hxB, hxC⟩ := hright a ha
      simpa only [hxA, hxB, hxC] using heq x u v
  exact ⟨LinearMap.mk₂ K (fun u v => c u v)
    (fun u u' v => by simp) hl (fun u v v' => by simp) hr, fun _ _ => rfl⟩

/-- The eigenvalue of a nonzero value of an equivariant bilinear pairing is
the product of the eigenvalues of its inputs. -/
public theorem eigenvalue_mul_eq
    (c : A →ₗ[K] B →ₗ[K] C)
    (rA : A → A) (rB : B → B) (rC : C → C)
    (heq : ∀ u v, c (rA u) (rB v) = rC (c u v))
    {u : A} {v : B} (hne : c u v ≠ 0)
    {a b d : K} (hu : rA u = a • u) (hv : rB v = b • v)
    (hw : rC (c u v) = d • c u v) : a * b = d := by
  apply smul_left_injective K hne
  calc
    (a * b) • c u v = c (a • u) (b • v) := by
      rw [LinearMap.map_smul₂, map_smul, smul_smul]
    _ = rC (c u v) := by rw [← hu, ← hv, heq]
    _ = d • c u v := hw

/-- In characteristic two, a nonzero scalar whose cube is its inverse is one. -/
public theorem eq_one_of_sq_mul_eq_inv [CharP K 2] {a : K}
    (ha : a ≠ 0) (h : a ^ 2 * a = a⁻¹) : a = 1 := by
  have hfour : a ^ 4 = 1 := by
    calc
      a ^ 4 = (a ^ 2 * a) * a := by simp only [pow_succ]
      _ = a⁻¹ * a := by rw [h]
      _ = 1 := inv_mul_cancel₀ ha
  have hz : (a - 1) ^ 4 = 0 := by
    simpa only [show 2 ^ 2 = 4 from rfl, hfour, one_pow, sub_self]
      using sub_pow_char_pow a (1 : K) 2 (p := 2)
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hz)
end ScalarEquivariantBilinear
