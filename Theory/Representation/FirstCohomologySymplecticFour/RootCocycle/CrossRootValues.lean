module

public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle.QuadraticValues
import Mathlib.Tactic.FinCases

/-!
# Extending a cocycle normal form across the symplectic roots

Over a finite characteristic-two field with more than two elements, agreement
on the two long-root pairs with a common principal correction determines all
eight elementary root families and forces the two quadratic coefficients to
coincide. This module is independent of the existence of that normalization.

Subtract the common principal cocycle. Words in each long-root pair produce
the coordinate tori, on which the resulting cocycle vanishes. For each short
or mixed root, a suitable product of these tori centralizes the root and has
no nonzero fixed vector, forcing its cocycle value to vanish. Finally the
matrix relation x₆(1)x₂(1) = x₀(1)x₂(1)x₄(1)x₆(1) identifies the coefficients.
Every group relation is verified on the elementary matrices from `Generation`.

This is a local step towards Aschbacher--Smith, *The Classification of Quasithin
Groups*, Lemma I.1.6(5), printed p.408 (PDF p.419).
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix
namespace Representation.OneCohomology.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)

private def weyl (p : Fin 2) (u : K) : Matrix.symplecticGroup (Fin 2) K :=
  rootElement (![0, 2] p) u * (rootElement (![1, 3] p) u⁻¹ * rootElement (![0, 2] p) u)

private def weylMatrix (p : Fin 2) (u : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ![fromBlocks !![0, 0; 0, 1] !![u, 0; 0, 0] !![u⁻¹, 0; 0, 0] !![0, 0; 0, 1],
    fromBlocks !![1, 0; 0, 0] !![0, 0; 0, u] !![0, 0; 0, u⁻¹] !![1, 0; 0, 0]] p

private lemma weyl_val (p : Fin 2) (u : K) (hu : u ≠ 0) :
    (weyl p u).val = weylMatrix p u := by
  change rootMatrix (![0, 2] p) u * (rootMatrix (![1, 3] p) u⁻¹ * rootMatrix (![0, 2] p) u) = _
  ext i j
  fin_cases p <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, weylMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.single, Matrix.one_apply, hu,
      CharTwo.add_self_eq_zero]

private def torus (p : Fin 2) (u : K) := weyl p u * weyl p 1

private def torusDiagonal (p : Fin 2) (u : K) : (Fin 2 ⊕ Fin 2) → K :=
  ![Sum.elim ![u, 1] ![u⁻¹, 1], Sum.elim ![1, u] ![1, u⁻¹]] p

private lemma torus_val (p : Fin 2) (u : K) (hu : u ≠ 0) :
    (torus p u).val = Matrix.diagonal (torusDiagonal p u) := by
  change (weyl p u).val * (weyl p 1).val = _
  rw [weyl_val p u hu, weyl_val p 1 one_ne_zero]
  ext i j
  fin_cases p <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, torusDiagonal, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.diagonal]

omit [CharP K 2] in
private lemma cocycle_mul (f : cocycles (symplecticNatural (k := K) 2))
    (g h : Matrix.symplecticGroup (Fin 2) K) :
    f.val (g * h) = g.val *ᵥ f.val h + f.val g := f.property g h

omit [CharP K 2] in
private lemma agree_mul (f q : cocycles (symplecticNatural (k := K) 2))
    {g h : Matrix.symplecticGroup (Fin 2) K}
    (hg : f.val g = q.val g) (hh : f.val h = q.val h) :
    f.val (g * h) = q.val (g * h) := by
  rw [cocycle_mul, cocycle_mul, hg, hh]

variable [Finite K]
private lemma quadratic_torus (p : Fin 2) (u : K) (hu : u ≠ 0) :
    (quadraticCocycle (K := K)).val (torus p u) = 0 := by
  funext i
  change (frobeniusEquiv K 2).symm (rowQuadratic ((torus p u).val i)) = 0
  rw [torus_val p u hu]
  rcases i with i | i <;> fin_cases i <;>
    simp [rowQuadratic, Matrix.diagonal]

private lemma cocycle_torus (f : cocycles (symplecticNatural (k := K) 2))
    (p : Fin 2) (z : K)
    (hup : ∀ t, f.val (rootElement (![0, 2] p) t) =
      (z • quadraticCocycle).val (rootElement (![0, 2] p) t))
    (hlo : ∀ t, f.val (rootElement (![1, 3] p) t) =
      (z • quadraticCocycle).val (rootElement (![1, 3] p) t))
    (u : K) (hu : u ≠ 0) : f.val (torus p u) = 0 := by
  have hw (x : K) : f.val (weyl p x) = (z • quadraticCocycle).val (weyl p x) :=
    agree_mul _ _ (hup x) (agree_mul _ _ (hlo x⁻¹) (hup x))
  have ht := agree_mul _ _ (hw u) (hw 1)
  change f.val (torus p u) = z • (quadraticCocycle (K := K)).val (torus p u) at ht
  simpa [quadratic_torus p u hu] using ht

private def centralTorus (r : Fin 4) (u : K) :=
  torus 0 u * torus 1 (![u⁻¹, u⁻¹, u, u] r)

private def centralDiagonal (r : Fin 4) (u : K) : (Fin 2 ⊕ Fin 2) → K :=
  ![Sum.elim ![u, u⁻¹] ![u⁻¹, u], Sum.elim ![u, u⁻¹] ![u⁻¹, u],
    Sum.elim ![u, u] ![u⁻¹, u⁻¹], Sum.elim ![u, u] ![u⁻¹, u⁻¹]] r

private lemma centralTorus_val (r : Fin 4) (u : K) (hu : u ≠ 0) :
    (centralTorus r u).val = Matrix.diagonal (centralDiagonal r u) := by
  have hv : ![u⁻¹, u⁻¹, u, u] r ≠ 0 := by fin_cases r <;> simpa using hu
  change (torus 0 u).val * (torus 1 _).val = _
  rw [torus_val 0 u hu, torus_val 1 _ hv, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases r <;> rcases i with i | i <;> fin_cases i <;>
    simp [torusDiagonal, centralDiagonal]

private lemma centralTorus_commutes (r : Fin 4) (u t : K) (hu : u ≠ 0) :
    centralTorus r u * rootElement ((![4, 5, 6, 7] : Fin 4 → Fin 8) r) t =
      rootElement ((![4, 5, 6, 7] : Fin 4 → Fin 8) r) t * centralTorus r u := by
  apply Subtype.ext
  change (centralTorus r u).val * rootMatrix ((![4, 5, 6, 7] : Fin 4 → Fin 8) r) t =
    rootMatrix ((![4, 5, 6, 7] : Fin 4 → Fin 8) r) t * (centralTorus r u).val
  rw [centralTorus_val r u hu]
  ext i j
  fin_cases r <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, centralDiagonal, rootMatrix,
      Matrix.fromBlocks, Matrix.single, Matrix.one_apply, CharTwo.neg_eq, mul_comm]

private lemma centralTorus_fixed_eq_zero (r : Fin 4) (u : K) (hu : u ≠ 0)
    (hu1 : u ≠ 1) (v : (Fin 2 ⊕ Fin 2) → K)
    (hv : (centralTorus r u).val *ᵥ v = v) : v = 0 := by
  rw [centralTorus_val r u hu] at hv
  have hn (i : Fin 2 ⊕ Fin 2) : centralDiagonal r u i ≠ 1 := by
    fin_cases r <;> rcases i with i | i <;> fin_cases i <;>
      simpa [centralDiagonal] using hu1
  funext i
  have hi := congrFun hv i
  simp only [Matrix.mulVec_diagonal] at hi
  by_contra hx
  exact hn i ((mul_eq_right₀ hx).mp hi)

private lemma short_values_zero (f : cocycles (symplecticNatural (k := K) 2))
    (u : K) (hu : u ≠ 0) (hu1 : u ≠ 1)
    (ht : ∀ p x, x ≠ 0 → f.val (torus p x) = 0)
    (r : Fin 4) (t : K) : f.val (rootElement ((![4, 5, 6, 7] : Fin 4 → Fin 8) r) t) = 0 := by
  have hv : ![u⁻¹, u⁻¹, u, u] r ≠ 0 := by fin_cases r <;> simpa using hu
  have hc : f.val (centralTorus r u) = 0 := by
    rw [centralTorus, cocycle_mul, ht 0 u hu, ht 1 _ hv, Matrix.mulVec_zero, add_zero]
  have he := congrArg f.val (centralTorus_commutes r u t hu)
  rw [cocycle_mul, cocycle_mul, hc, Matrix.mulVec_zero, zero_add, add_zero] at he
  exact centralTorus_fixed_eq_zero r u hu hu1 _ he

private lemma coefficient_relation :
    rootElement 6 (1 : K) * rootElement 2 1 =
      rootElement 0 1 * (rootElement 2 1 * (rootElement 4 1 * rootElement 6 1)) := by
  apply Subtype.ext
  change rootMatrix 6 (1 : K) * rootMatrix 2 1 =
    rootMatrix 0 1 * (rootMatrix 2 1 * (rootMatrix 4 1 * rootMatrix 6 1))
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single, Matrix.one_apply,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private lemma coefficients_eq (f : cocycles (symplecticNatural (k := K) 2))
    (z₀ z₁ : K)
    (h0 : f.val (rootElement 0 1) = (z₀ • quadraticCocycle).val (rootElement 0 1))
    (h2 : f.val (rootElement 2 1) = (z₁ • quadraticCocycle).val (rootElement 2 1))
    (h4 : f.val (rootElement 4 1) = 0) (h6 : f.val (rootElement 6 1) = 0) :
    z₀ = z₁ := by
  have he := congrArg f.val (coefficient_relation (K := K))
  simp only [cocycle_mul, h0, h2, h4, h6, Matrix.mulVec_zero, add_zero, zero_add] at he
  have ha := congrFun he a
  change (rootMatrix 6 (1 : K) *ᵥ (z₁ • (quadraticCocycle (K := K)).val (rootElement 2 1))) a =
    (rootMatrix 0 (1 : K) *ᵥ (z₁ • (quadraticCocycle (K := K)).val (rootElement 2 1)) +
      z₀ • (quadraticCocycle (K := K)).val (rootElement 0 1)) a at ha
  simp [quadraticCocycle_rootElement, rootQuadraticValue, rootMatrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.single, Matrix.one_apply] at ha
  exact ha.symm

private lemma exists_parameter (hcard : 2 < Nat.card K) :
    ∃ u : K, u ≠ 0 ∧ u ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  have hc : 2 < Fintype.card K := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra! h
  have hx := h x
  have hy := h y
  have hz := h z
  by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> by_cases hz0 : z = 0 <;> simp_all

/-- Agreement on the two long-root pairs with a common principal correction
forces the quadratic coefficients to coincide and determines all eight roots. -/
theorem extend_longRoot_normal_form (hcard : 2 < Nat.card K)
    (f : cocycles (symplecticNatural (k := K) 2)) (t0 t1 : K)
    (v : (Fin 2 ⊕ Fin 2) → K)
    (h0 : ∀ t, f.val (rootElement 0 t) =
      (t0 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 0 t))
    (h1 : ∀ t, f.val (rootElement 1 t) =
      (t0 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 1 t))
    (h2 : ∀ t, f.val (rootElement 2 t) =
      (t1 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 2 t))
    (h3 : ∀ t, f.val (rootElement 3 t) =
      (t1 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 3 t)) :
    t0 = t1 ∧ ∀ (r : Fin 8) (t : K), f.val (rootElement r t) =
      (t0 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement r t) := by
  let f' := f - principal (symplecticNatural 2) v
  have h0' (t : K) : f'.val (rootElement 0 t) =
      (t0 • quadraticCocycle).val (rootElement 0 t) := sub_eq_iff_eq_add.mpr (h0 t)
  have h1' (t : K) : f'.val (rootElement 1 t) =
      (t0 • quadraticCocycle).val (rootElement 1 t) := sub_eq_iff_eq_add.mpr (h1 t)
  have h2' (t : K) : f'.val (rootElement 2 t) =
      (t1 • quadraticCocycle).val (rootElement 2 t) := sub_eq_iff_eq_add.mpr (h2 t)
  have h3' (t : K) : f'.val (rootElement 3 t) =
      (t1 • quadraticCocycle).val (rootElement 3 t) := sub_eq_iff_eq_add.mpr (h3 t)
  have ht (p : Fin 2) (x : K) (hx : x ≠ 0) : f'.val (torus p x) = 0 := by
    fin_cases p
    · exact cocycle_torus f' 0 t0 h0' h1' x hx
    · exact cocycle_torus f' 1 t1 h2' h3' x hx
  obtain ⟨u, hu, hu1⟩ := exists_parameter (K := K) hcard
  have hs := short_values_zero f' u hu hu1 ht
  have he : t0 = t1 := coefficients_eq f' t0 t1 (h0' 1) (h2' 1) (hs 0 1) (hs 2 1)
  refine ⟨he, ?_⟩
  intro r t
  apply sub_eq_iff_eq_add.mp
  change f'.val (rootElement r t) = (t0 • quadraticCocycle).val (rootElement r t)
  fin_cases r
  · exact h0' t
  · exact h1' t
  · rw [he]
    exact h2' t
  · rw [he]
    exact h3' t
  · change f'.val (rootElement 4 t) = t0 • quadraticCocycle.val (rootElement 4 t)
    have hz : f'.val (rootElement 4 t) = 0 := hs 0 t
    rw [hz]
    funext i
    simp [quadraticCocycle_rootElement, rootQuadraticValue]
  · change f'.val (rootElement 5 t) = t0 • quadraticCocycle.val (rootElement 5 t)
    have hz : f'.val (rootElement 5 t) = 0 := hs 1 t
    rw [hz]
    funext i
    simp [quadraticCocycle_rootElement, rootQuadraticValue]
  · change f'.val (rootElement 6 t) = t0 • quadraticCocycle.val (rootElement 6 t)
    have hz : f'.val (rootElement 6 t) = 0 := hs 2 t
    rw [hz]
    funext i
    simp [quadraticCocycle_rootElement, rootQuadraticValue]
  · change f'.val (rootElement 7 t) = t0 • quadraticCocycle.val (rootElement 7 t)
    have hz : f'.val (rootElement 7 t) = 0 := hs 3 t
    rw [hz]
    funext i
    simp [quadraticCocycle_rootElement, rootQuadraticValue]

end Representation.OneCohomology.SymplecticFour
