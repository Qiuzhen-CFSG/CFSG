module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two

/-!
# Separation of Ree field and inner-diagonal automorphisms

Matrix conjugation preserves trace, whereas the canonical field automorphism
squares it. The values `t² + t^(2^(m+1))` detect every nonidentity Frobenius
power on the coefficient field of order `2^(2*m+1)`. Indeed, an endomorphism
fixing all these values has `σ(t) + t` fixed by the `m`th Frobenius power,
hence in the binary field. Consequently `σ² = 1`; the odd Frobenius period
then gives `σ = 1`.

The actual fixed end-root words constructed in `FieldSeparation.RootWitness`
have exactly these traces by `FieldSeparation.TraceValues`. Applying the trace
criterion to those witnesses proves that the canonical field subgroup and
the actual inner-diagonal subgroup intersect trivially. Neither simplicity
nor automorphism coverage is needed. The proof also applies at `m = 0` to
the full fixed group, separately from the Tits simple carrier.

Source: GLS3, Theorem 2.5.12(a) and the Suzuki–Ree convention in Definition
2.5.13 (`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith, A.3.15(5), printed
pp.50–51, and the proof of Proposition 1.3.4, printed p.511
(`refs/quasithin.pdf`). The trace argument uses the actual integral F₄
Cartan-plus-root representation.
-/

public section
namespace ReeF4.Cartan
open Theory.AlgebraicGroup Subgroup
variable {m : ℕ}

private theorem half_frobenius_fixed {m : ℕ} (x : CoefficientField m)
    (h : x ^ (2 ^ m) = x) : x ^ 2 = x := by
  have hh : x ^ (2 ^ (2 * m)) = x := by
    calc
      x ^ (2 ^ (2 * m)) = (x ^ (2 ^ m)) ^ (2 ^ m) := by
        rw [← pow_mul, ← pow_add]
        exact congrArg (fun n : ℕ => x ^ (2 ^ n)) (two_mul m)
      _ = x := by rw [h, h]
  calc
    x ^ 2 = (x ^ (2 ^ (2 * m))) ^ 2 := by rw [hh]
    _ = x ^ (2 ^ (2 * m + 1)) := by
      simpa only [pow_succ 2 (2 * m)] using (pow_mul x (2 ^ (2 * m)) 2).symm
    _ = x := field_pow m x

private theorem fieldEnd_square_of_trace_values {m : ℕ}
    (σ : CoefficientField m →+* CoefficientField m)
    (hσ : ∀ t, σ (t ^ 2 + t ^ (2 ^ (m + 1))) = t ^ 2 + t ^ (2 ^ (m + 1))) :
    σ ^ 2 = 1 := by
  apply RingHom.ext
  intro t
  have ht : σ t + (σ t) ^ (2 ^ m) = t + t ^ (2 ^ m) := by
    apply (frobenius (CoefficientField m) 2).injective
    change (σ t + (σ t) ^ (2 ^ m)) ^ 2 = (t + t ^ (2 ^ m)) ^ 2
    rw [add_pow_char, add_pow_char]
    simpa only [map_add, map_pow, pow_succ 2 m, pow_mul] using hσ t
  have hd : (σ t + t) ^ (2 ^ m) = σ t + t := by
    rw [add_pow_char_pow]
    have he := congrArg (fun z => z + σ t + t ^ (2 ^ m)) ht
    simpa only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_cancel_right] using he
  have hd2 := half_frobenius_fixed (σ t + t) hd
  have hor := eq_zero_or_one_of_sq_eq_self hd2
  change σ (σ t) = t
  rcases hor with h | h
  · have he : σ t = t := by
      have hh := congrArg (· + t) h
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
    rw [he, he]
  · have he : σ t = t + 1 := by
      have hh := congrArg (· + t) h
      simpa only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
        CharTwo.add_cancel_right, zero_add, add_zero] using hh
    rw [he, map_add, map_one, he]
    simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem field_power_eq_one_of_trace_values {m : ℕ} (k : ℕ)
    (h : ∀ t : CoefficientField m,
      (t ^ 2 + t ^ (2 ^ (m + 1))) ^ (2 ^ k) = t ^ 2 + t ^ (2 ^ (m + 1))) :
    iterateFrobenius (CoefficientField m) 2 k = 1 := by
  let σ := iterateFrobenius (CoefficientField m) 2 k
  have hs : σ ^ 2 = 1 := fieldEnd_square_of_trace_values σ h
  have hp : (frobenius (CoefficientField m) 2) ^ (2 * m + 1) = 1 := by
    rw [← iterateFrobenius_eq_pow]
    exact RingHom.ext (field_pow m)
  have hp' : σ ^ (2 * m + 1) = 1 := by
    dsimp [σ]
    rw [iterateFrobenius_eq_pow, ← pow_mul, Nat.mul_comm k, pow_mul, hp, one_pow]
  have he : σ ^ (2 * m + 1) = σ := by
    rw [pow_succ, pow_mul, hs, one_pow, one_mul]
  exact he.symm.trans hp'

/-- Iterated Frobenius raises every matrix entry to the same field power. -/
theorem field_pow_entry (d : LocalBlockInput m) (k : ℕ) (x : d.fixedGroup)
    (i j : F4Chevalley.BasisIndex) :
    (((d.fieldAutomorphism ^ k) x).val.val : MatrixCarrier m) i j =
      (x.val.val : MatrixCarrier m) i j ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, d.fieldAutomorphism_entry, ih, ← pow_mul,
      ← pow_succ 2 k]

/-- Frobenius acts on matrix traces by its scalar field power. -/
theorem field_pow_trace (d : LocalBlockInput m) (k : ℕ) (x : d.fixedGroup) :
    Matrix.trace (((d.fieldAutomorphism ^ k) x).val.val : MatrixCarrier m) =
      Matrix.trace (x.val.val : MatrixCarrier m) ^ (2 ^ k) := by
  have he : (((d.fieldAutomorphism ^ k) x).val.val : MatrixCarrier m) =
      (x.val.val : MatrixCarrier m).map (iterateFrobenius (CoefficientField m) 2 k) := by
    ext i j
    exact field_pow_entry d k x i j
  rw [he, ← AddMonoidHom.map_trace]
  rfl

/-- Every inner-diagonal automorphism preserves the trace of the defining matrix. -/
theorem innerDiagonal_trace (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (ha : a ∈ innerDiagonal d) (x : d.fixedGroup) :
    Matrix.trace ((a x).val.val : MatrixCarrier m) =
      Matrix.trace (x.val.val : MatrixCarrier m) := by
  obtain ⟨g, hg⟩ := innerDiagonal_matrix_conjugation d a ha
  rw [hg, Units.val_mul, Units.val_mul]
  exact Matrix.trace_units_conj g _

/-- The indicated trace values suffice to separate field and inner-diagonal
 automorphisms. The fixed-group trace witnesses remain an explicit hypothesis. -/
theorem field_disjoint_innerDiagonal_of_trace_values (d : LocalBlockInput m)
    (htrace : ∀ t : CoefficientField m, ∃ x : d.fixedGroup,
      Matrix.trace (x.val.val : MatrixCarrier m) = t ^ 2 + t ^ (2 ^ (m + 1))) :
    Disjoint (zpowers d.fieldAutomorphism) (innerDiagonal d) := by
  apply Subgroup.disjoint_def.mpr
  intro a ha hi
  obtain ⟨k, hk⟩ :=
    (isOfFinOrder_of_finite d.fieldAutomorphism).mem_powers_iff_mem_zpowers.mpr ha
  rw [← hk] at hi ⊢
  have hs : iterateFrobenius (CoefficientField m) 2 k = 1 := by
    apply field_power_eq_one_of_trace_values k
    intro t
    obtain ⟨x, hx⟩ := htrace t
    have he := innerDiagonal_trace d (d.fieldAutomorphism ^ k) hi x
    rw [field_pow_trace, hx] at he
    exact he
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [field_pow_entry]
  exact DFunLike.congr_fun hs ((x.val.val : MatrixCarrier m) i j)

/-- The canonical field subgroup intersects the actual inner-diagonal subgroup
trivially. This applies to the Ree simple-family range `1 ≤ m`; at `m = 0`
it concerns the full fixed group, independently of the Tits simple carrier. -/
theorem field_disjoint_innerDiagonal (d : LocalBlockInput m) :
    Disjoint (zpowers d.fieldAutomorphism) (innerDiagonal d) := by
  apply field_disjoint_innerDiagonal_of_trace_values d
  intro t
  exact ⟨FieldSeparation.traceWitness d t, FieldSeparation.traceWitness_trace d t⟩

end ReeF4.Cartan
