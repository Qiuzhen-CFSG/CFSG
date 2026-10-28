module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Ring

/-!
# Odd index under an odd-degree finite-field extension

For finite fields K and F with a K-algebra structure, if |K| and [F:K] are
odd, the actual coefficient embedding GL₂(K) → GL₂(F) has odd-index range.
This is the counting step in the fixed-field construction of a Sylow two
subgroup fixed pointwise by odd coefficient automorphisms, used in ABG II.3,
Proposition 3(iv), article pp. 27–28.

Write k=|K| and r=[F:K]. The formula |GL₂(K)|=k(k−1)(k²−1) expresses the
cardinality ratio as k^(r−1) times the geometric sums of length r at k and
k². Each factor is odd. Injectivity of the actual matrix coefficient map
identifies the range cardinality, and the index formula gives the result.
-/

open scoped BigOperators

namespace Matrix.GeneralLinearGroup

private theorem card_gl_two (K : Type*) [Field K] [Finite K] :
    Nat.card (GL (Fin 2) K) = Nat.card K * (Nat.card K - 1) * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ← Nat.card_eq_fintype_card]
  have h : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [h]
  ring

private theorem odd_geom_sum {k r : ℕ} (hk : Odd k) (hr : Odd r) :
    Odd (∑ i ∈ Finset.range r, k ^ i) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  simpa only [Finset.filter_true_of_mem (fun _ _ => hk.pow), Finset.card_range] using hr

private theorem gl_two_card_ratio {k r : ℕ} (hk : 1 ≤ k) (hr : 0 < r) :
    k ^ r * (k ^ r - 1) * ((k ^ r) ^ 2 - 1) =
      (k * (k - 1) * (k ^ 2 - 1)) *
      (k ^ (r - 1) * (∑ i ∈ Finset.range r, k ^ i) *
        (∑ i ∈ Finset.range r, (k ^ 2) ^ i)) := by
  have h1 := geom_sum_mul_of_one_le hk r
  have h2 := geom_sum_mul_of_one_le (one_le_pow₀ (n := 2) hk) r
  have he : k ^ r = k * k ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  calc
    _ = (k * k ^ (r - 1)) *
        ((∑ i ∈ Finset.range r, k ^ i) * (k - 1)) *
        ((∑ i ∈ Finset.range r, (k ^ 2) ^ i) * (k ^ 2 - 1)) := by
      rw [h1, h2, ← pow_mul, ← pow_mul, Nat.mul_comm 2 r, ← he]
    _ = _ := by ring

/-- The coefficient embedding of GL₂ has odd index for an odd-degree extension
of finite fields of odd cardinality. -/
public theorem odd_index_map_of_odd_finrank
    (K F : Type*) [Field K] [Field F] [Finite K] [Finite F] [Algebra K F]
    (hK : Odd (Nat.card K)) (hF : Odd (Module.finrank K F)) :
    Odd (map (n := Fin 2) (algebraMap K F)).range.index := by
  let f := map (n := Fin 2) (algebraMap K F)
  have hf : Function.Injective f := by
    intro x y h
    ext i j
    exact (algebraMap K F).injective (congrArg (fun z : GL (Fin 2) F => z i j) h)
  have hc : Nat.card f.range = Nat.card (GL (Fin 2) K) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hpos : 0 < Nat.card (GL (Fin 2) K) := Nat.card_pos
  have hratio := gl_two_card_ratio (Nat.card_pos (α := K))
    (Module.finrank_pos (R := K) (M := F))
  have heq : f.range.index =
      Nat.card K ^ (Module.finrank K F - 1) *
      (∑ i ∈ Finset.range (Module.finrank K F), Nat.card K ^ i) *
      (∑ i ∈ Finset.range (Module.finrank K F), (Nat.card K ^ 2) ^ i) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hc, Subgroup.card_mul_index, hc, card_gl_two K, card_gl_two F,
      Module.natCard_eq_pow_finrank (K := K) (V := F)]
    exact hratio
  rw [heq]
  exact (hK.pow.mul (odd_geom_sum hK hF)).mul (odd_geom_sum hK.pow hF)

end Matrix.GeneralLinearGroup
