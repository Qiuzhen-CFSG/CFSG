module

public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle.QuadraticValues
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Normalization on the four long-root families

Over a finite characteristic-two field with more than two elements, any cocycle
on the natural symplectic four-space agrees on the two long-root pairs with two
scalar multiples of the quadratic cocycle, after a single principal correction.

Choose a diagonal torus element with no fixed vectors. Solving its displacement
equation gives the principal correction; commutation then makes the corrected
cocycle vanish on the entire diagonal torus. The involution relation and the
other coordinate's torus force the value of an upper long root at parameter one
to be supported on its root coordinate. Torus conjugation and inverse Frobenius
give every parameter value. The block swap, on which the corrected cocycle also
vanishes, gives the lower roots with the same coefficients.

All group relations are checked on the matrices in `Generation`. This is a local
step towards Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408; it does not use a generation theorem.
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Matrix
namespace Representation.OneCohomology.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2]
local notation "V" => (Fin 2 ⊕ Fin 2) → K
local notation "G" => Matrix.symplecticGroup (Fin 2) K
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private lemma fixed_scalar_zero {u x : K} (hu : u ≠ 1) (h : u * x = x) : x = 0 := by
  by_contra hx
  exact hu ((mul_eq_right₀ hx).mp h)

private def torus (u v : Kˣ) : G :=
  ⟨Matrix.diagonal (Sum.elim ![(u : K), (v : K)] ![(↑u⁻¹ : K), (↑v⁻¹ : K)]), by
    rw [SymplecticGroup.mem_iff]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Matrix.diagonal,
        Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq]⟩

private lemma torus_action (u v : Kˣ) (x : V) :
    (torus u v).val *ᵥ x =
      Sum.elim ![(u : K) * x a, (v : K) * x b]
        ![(↑u⁻¹ : K) * x c, (↑v⁻¹ : K) * x d] := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [torus, Matrix.mulVec_diagonal]

private lemma torus_commute (u v u' v' : Kˣ) :
    torus u v * torus u' v' = torus u' v' * torus u v := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  simp only [diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private lemma cocycle_mul (f : cocycles (symplecticNatural (k := K) 2)) (g h : G) :
    f.val (g * h) = g.val *ᵥ f.val h + f.val g := f.property g h

private lemma cocycle_one (f : cocycles (symplecticNatural (k := K) 2)) :
    f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

private lemma cocycle_commute (f : cocycles (symplecticNatural (k := K) 2))
    (g h : G) (he : g * h = h * g) :
    g.val *ᵥ f.val h + f.val g = h.val *ᵥ f.val g + f.val h := by
  simpa only [cocycle_mul] using congrArg f.val he

private lemma torus_fixed_eq_zero (s : Kˣ) (hs : (s : K) ≠ 1) (x : V)
    (hx : (torus s s).val *ᵥ x = x) : x = 0 := by
  have hi : (↑s⁻¹ : K) ≠ 1 := by simpa using hs
  funext i
  have h := congrFun hx i
  rcases i with i | i <;> fin_cases i <;> simp only [torus_action, Sum.elim_inl,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  all_goals
    change _ = 0
    first
    | exact fixed_scalar_zero hs h
    | exact fixed_scalar_zero hi h

private lemma torus_cocycle_zero (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : f.val (torus s s) = 0) (u v : Kˣ) :
    f.val (torus u v) = 0 := by
  apply torus_fixed_eq_zero s hs
  simpa [hf] using cocycle_commute f (torus s s) (torus u v) (torus_commute _ _ _ _)

private def upper (i : Fin 2) (t : K) : G := rootElement (![0, 2] i) t
private def lower (i : Fin 2) (t : K) : G := rootElement (![1, 3] i) t

private lemma upper_zero (i : Fin 2) : upper i (0 : K) = 1 := by
  apply Subtype.ext
  fin_cases i <;> simp [upper, rootElement, rootMatrix, Matrix.single_zero]

private lemma upper_square (i : Fin 2) : upper i (1 : K) * upper i 1 = 1 := by
  apply Subtype.ext
  change rootMatrix (![0, 2] i) (1 : K) * rootMatrix (![0, 2] i) 1 =
    (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  ext j k
  fin_cases i <;> rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [rootMatrix, Matrix.mul_apply, Matrix.fromBlocks, Matrix.single,
      Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private lemma torus_upper (u v : Kˣ) (i : Fin 2) (t : K) :
    torus u v * upper i t = upper i ((![↑u, ↑v] i : K)^2 * t) * torus u v := by
  apply Subtype.ext
  ext j k
  change ((torus u v).val * (upper i t).val) j k =
    ((upper i ((![↑u, ↑v] i : K)^2 * t)).val * (torus u v).val) j k
  simp only [torus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [upper, rootElement, rootMatrix, Matrix.fromBlocks,
      Matrix.single, pow_two, mul_assoc, mul_comm, mul_left_comm]

private def swap : G := ⟨fromBlocks 0 1 1 0, by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp only [neg_zero, mul_zero, zero_mul, add_zero, one_mul, transpose_one,
    transpose_zero, zero_add, sub_zero, zero_sub, true_and]
  ext i j
  simp [CharTwo.neg_eq]⟩

private lemma swap_action (x : V) :
    (swap (K := K)).val *ᵥ x = Sum.elim (fun i => x (Sum.inr i)) (fun i => x (Sum.inl i)) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [swap, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_two]

private lemma torus_swap (s : Kˣ) :
    torus s s * swap = swap * torus s⁻¹ s⁻¹ := by
  apply Subtype.ext
  ext j k
  change ((torus s s).val * (swap (K := K)).val) j k =
    ((swap (K := K)).val * (torus s⁻¹ s⁻¹).val) j k
  rcases j with j | j <;> rcases k with k | k <;> fin_cases j <;> fin_cases k <;>
    simp [torus, swap, Matrix.mul_apply, Matrix.fromBlocks, Matrix.diagonal,
      Fintype.sum_sum_type, Fin.sum_univ_two]

private lemma swap_upper (i : Fin 2) (t : K) :
    swap * upper i t = lower i t * swap := by
  apply Subtype.ext
  ext j k
  change ((swap (K := K)).val * (upper i t).val) j k =
    ((lower i t).val * (swap (K := K)).val) j k
  fin_cases i <;> rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [swap, upper, lower, rootElement, rootMatrix, Matrix.mul_apply, Matrix.fromBlocks,
      Matrix.single, Fintype.sum_sum_type, Fin.sum_univ_two]

private lemma swap_cocycle_zero (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0) :
    f.val swap = 0 := by
  apply torus_fixed_eq_zero s hs
  have h := congrArg f.val (torus_swap s)
  simpa only [cocycle_mul, hf, mulVec_zero, zero_add, add_zero] using h

private lemma upper_action (i : Fin 2) (t : K) (x : V) :
    (upper i t).val *ᵥ x = fun j => x j + (Pi.single (Sum.inl i) (t * x (Sum.inr i)) : V) j := by
  funext j
  fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [upper, rootElement, rootMatrix, Matrix.mulVec, dotProduct, Matrix.fromBlocks,
      Matrix.single, Fintype.sum_sum_type, Fin.sum_univ_two]

private lemma upper_one_support (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0) (i : Fin 2) :
    f.val (upper i 1) = Pi.single (Sum.inl i) (f.val (upper i 1) (Sum.inl i)) := by
  have hi : (↑s⁻¹ : K) ≠ 1 := by simpa using hs
  have hc : torus (![1, s] i) (![s, 1] i) * upper i (1 : K) =
      upper i 1 * torus (![1, s] i) (![s, 1] i) := by
    have h := torus_upper (![1, s] i) (![s, 1] i) i (1 : K)
    fin_cases i <;> simpa using h
  have ht := cocycle_commute f _ _ hc
  simp only [hf, mulVec_zero, zero_add, add_zero, torus_action] at ht
  have hq := congrArg f.val (upper_square (K := K) i)
  rw [cocycle_mul, cocycle_one] at hq
  have hl : f.val (upper i 1) (Sum.inr i) = 0 := by
    have h := congrFun hq (Sum.inl i)
    simpa only [upper_action, Pi.add_apply, Pi.single_eq_same, one_mul,
      add_right_comm, CharTwo.add_self_eq_zero, zero_add, Pi.zero_apply] using h
  funext j
  rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals simp only [Pi.single_apply, reduceCtorEq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    if_true, if_false]
  all_goals first | rfl | exact hl | skip
  all_goals
    first
    | have h := congrFun ht b
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Sum.elim_inl, Sum.elim_inr] at h
      exact fixed_scalar_zero hs h
    | have h := congrFun ht a
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Sum.elim_inl, Sum.elim_inr] at h
      exact fixed_scalar_zero hs h
    | have h := congrFun ht d
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Sum.elim_inl, Sum.elim_inr] at h
      exact fixed_scalar_zero hi h
    | have h := congrFun ht c
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Sum.elim_inl, Sum.elim_inr] at h
      exact fixed_scalar_zero hi h

variable [Finite K]

private lemma upper_values (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0)
    (i : Fin 2) (t : K) :
    f.val (upper i t) = Pi.single (Sum.inl i)
      ((frobeniusEquiv K 2).symm t * f.val (upper i 1) (Sum.inl i)) := by
  by_cases ht : t = 0
  · subst t
    simp [upper_zero, cocycle_one]
  let u : Kˣ := Units.mk0 ((frobeniusEquiv K 2).symm t) (by simpa using ht)
  have hscale : (![↑u, ↑u] i : K)^2 * 1 = t := by
    fin_cases i <;> simp [u]
  have h := congrArg f.val (torus_upper u u i (1 : K))
  rw [hscale] at h
  simp only [cocycle_mul, hf, mulVec_zero, zero_add, add_zero] at h
  rw [← h, upper_one_support f s hs hf i, torus_action]
  funext j
  fin_cases i <;> rcases j with j | j <;> fin_cases j <;> simp [u]

private lemma lower_values (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0)
    (i : Fin 2) (t : K) :
    f.val (lower i t) = Pi.single (Sum.inr i)
      ((frobeniusEquiv K 2).symm t * f.val (upper i 1) (Sum.inl i)) := by
  have h := congrArg f.val (swap_upper i t)
  simp only [cocycle_mul, swap_cocycle_zero f s hs hf, mulVec_zero,
    zero_add, add_zero] at h
  rw [← h, upper_values f s hs hf, swap_action]
  funext j
  fin_cases i <;> rcases j with j | j <;> fin_cases j <;> simp

private lemma exists_torus_normalization
    (f : cocycles (symplecticNatural (k := K) 2)) (s : Kˣ) (hs : (s : K) ≠ 1) :
    ∃ v : V, ∀ u w, (f - principal (symplecticNatural 2) v).val (torus u w) = 0 := by
  let x := f.val (torus s s)
  let v : V := Sum.elim (fun i => x (Sum.inl i) / ((s : K) - 1))
    (fun i => x (Sum.inr i) / ((↑s⁻¹ : K) - 1))
  have hi : (↑s⁻¹ : K) ≠ 1 := by simpa using hs
  have hp : (principal (symplecticNatural 2) v).val (torus s s) = x := by
    change (torus s s).val *ᵥ v - v = x
    rw [torus_action]
    funext j
    rcases j with j | j <;> fin_cases j <;>
      simp [v] <;> field_simp
  refine ⟨v, torus_cocycle_zero _ s hs ?_⟩
  change f.val (torus s s) - (principal (symplecticNatural 2) v).val (torus s s) = 0
  rw [hp]
  exact sub_self _

private lemma exists_nontrivial_unit (hcard : 2 < Nat.card K) :
    ∃ s : Kˣ, (s : K) ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  have hc : 2 < Fintype.card K := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  have hex : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra! h
    have hx := h x
    have hy := h y
    have hz := h z
    by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> by_cases hz0 : z = 0 <;> simp_all
  obtain ⟨s, hs0, hs1⟩ := hex
  exact ⟨Units.mk0 s hs0, hs1⟩

private lemma normalized_upper_quadratic
    (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0)
    (i : Fin 2) (t : K) :
    f.val (upper i t) =
      (f.val (upper i 1) (Sum.inl i) • quadraticCocycle).val (upper i t) := by
  rw [upper_values f s hs hf]
  change _ = f.val (upper i 1) (Sum.inl i) • quadraticCocycle.val (rootElement _ t)
  rw [quadraticCocycle_rootElement]
  funext j
  fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [rootQuadraticValue, mul_comm]

private lemma normalized_lower_quadratic
    (f : cocycles (symplecticNatural (k := K) 2))
    (s : Kˣ) (hs : (s : K) ≠ 1) (hf : ∀ u v, f.val (torus u v) = 0)
    (i : Fin 2) (t : K) :
    f.val (lower i t) =
      (f.val (upper i 1) (Sum.inl i) • quadraticCocycle).val (lower i t) := by
  rw [lower_values f s hs hf]
  change _ = f.val (upper i 1) (Sum.inl i) • quadraticCocycle.val (rootElement _ t)
  rw [quadraticCocycle_rootElement]
  funext j
  fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [rootQuadraticValue, mul_comm]

/-- On each long-root pair an arbitrary cocycle is a scalar multiple of the
quadratic cocycle plus a principal cocycle, with the same principal vector for
both pairs. -/
theorem exists_longRoot_normal_form (hcard : 2 < Nat.card K)
    (f : cocycles (symplecticNatural (k := K) 2)) :
    ∃ (t0 t1 : K) (v : V),
      (∀ t, f.val (rootElement 0 t) =
        (t0 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 0 t)) ∧
      (∀ t, f.val (rootElement 1 t) =
        (t0 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 1 t)) ∧
      (∀ t, f.val (rootElement 2 t) =
        (t1 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 2 t)) ∧
      (∀ t, f.val (rootElement 3 t) =
        (t1 • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement 3 t)) := by
  obtain ⟨s, hs⟩ := exists_nontrivial_unit (K := K) hcard
  obtain ⟨v, hv⟩ := exists_torus_normalization f s hs
  let f' := f - principal (symplecticNatural 2) v
  refine ⟨f'.val (upper 0 1) a, f'.val (upper 1 1) b, v, ?_, ?_, ?_, ?_⟩
  · intro t
    have h := normalized_upper_quadratic f' s hs hv 0 t
    exact sub_eq_iff_eq_add.mp h
  · intro t
    have h := normalized_lower_quadratic f' s hs hv 0 t
    exact sub_eq_iff_eq_add.mp h
  · intro t
    have h := normalized_upper_quadratic f' s hs hv 1 t
    exact sub_eq_iff_eq_add.mp h
  · intro t
    have h := normalized_lower_quadratic f' s hs hv 1 t
    exact sub_eq_iff_eq_add.mp h

end Representation.OneCohomology.SymplecticFour
