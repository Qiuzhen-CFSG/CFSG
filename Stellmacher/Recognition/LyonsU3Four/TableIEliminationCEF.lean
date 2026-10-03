module

public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
import Mathlib.Tactic.FieldSimp

/-!
# Elimination of Table I cases C, E and F

Both choices of Z₁/Z₂ in C and E, and the matrix F, give the same numerical
system. Signed Galois symmetry first identifies the degrees in each orbit.
If `x` is the degree in the four rows with `dᵗ = -1`, and `s` is the degree
in the row with `dᵗ = -2`, ordinary orthogonality gives `s = -2x`.
The positive weighted column `₁dᶻ - dᵗ` is then `-128/x`, so `x < 0`.
The difference of the first two involution columns gives
`1 + 18/x + 1/y - 16/u - 16/v = 0`.

We can finish before the Schur argument printed on p. 383: the signed
multiplicity bound for the `dᵗ = -2`, `χ(z) = 10` row gives `s ≥ 90`.
Together with `s = -2x` and `x ≡ 51 (mod 64)`, this gives `x ≤ -77`.
The reciprocal equation would then have left side at least
`1 - 18/77 - 1/63 - 32/52 > 0`. Thus the full degree and order constraints
already contradict one another; no prime bound or row-separation premise is
needed. In particular, the printed terminal possibility `x = -13` would
force `s = 26`, contrary to its signed multiplicity constraint.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I pp. 375, 377 and the elimination on p. 383.
The page images were checked in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData TableICatalogue


private theorem reciprocal_bounds (n : ℤ) (a b C : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (hn : (n : ℚ) ≤ -a ∨ b ≤ n) :
    -C/a ≤ C/n ∧ C/n ≤ C/b := by
  simp only [neg_div]
  rcases hn with hn | hn
  · have hn0 : (n : ℚ) ≤ 0 := by linarith
    have h1 := div_le_div_of_nonneg_left hC ha (show a ≤ -(n : ℚ) by linarith)
    have h2 := div_nonpos_of_nonneg_of_nonpos hC hn0
    have h3 : 0 ≤ C/b := div_nonneg hC hb.le
    simp only [div_neg] at h1
    constructor <;> linarith
  · have h1 := div_le_div_of_nonneg_left hC hb hn
    have h2 : 0 ≤ C/(n : ℚ) := div_nonneg hC (by linarith)
    have h3 : 0 ≤ C/a := div_nonneg hC ha.le
    constructor <;> linarith

private theorem cef_arithmetic (x s y u v : ℤ)
    (hs : s ≤ -38 ∨ 90 ≤ s)
    (hy : y ≤ -63 ∨ 65 ≤ y)
    (hu : u ≤ -12 ∨ 52 ≤ u) (hv : v ≤ -12 ∨ 52 ≤ v)
    (hxm : (x-51)%64=0) (hrel : s = -2*x)
    (hpos : 0 < 72/(x:ℚ)+400/(s:ℚ))
    (heq : 1+18/(x:ℚ)+1/(y:ℚ)-16/(u:ℚ)-16/(v:ℚ)=0) : False := by
  have hrelq : (s : ℚ) = -2 * x := by exact_mod_cast hrel
  have hreduce : (72:ℚ)/x + 400/s = -128/x := by rw [hrelq]; field_simp; ring
  rw [hreduce] at hpos
  have hxn : x < 0 := by
    by_contra hn
    have hq : (0 : ℚ) ≤ x := by exact_mod_cast (show 0 ≤ x by omega)
    have := div_nonpos_of_nonpos_of_nonneg (by norm_num : (-128:ℚ) ≤ 0) hq
    linarith
  have hxx : x ≤ -77 := by omega
  have hbx := (reciprocal_bounds x 77 1 18 (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by exact_mod_cast hxx))).1
  have hby := (reciprocal_bounds y 63 65 1 (by norm_num) (by norm_num)
    (by norm_num) (by exact_mod_cast hy)).1
  have hbu := (reciprocal_bounds u 12 52 16 (by norm_num) (by norm_num)
    (by norm_num) (by exact_mod_cast hu)).2
  have hbv := (reciprocal_bounds v 12 52 16 (by norm_num) (by norm_num)
    (by norm_num) (by exact_mod_cast hv)).2
  linarith

private theorem degree_step {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    (degree : I → ℤ) (h : d.SignedGaloisSymmetry degree) (a b : I)
    (hpos : ∀ k, (d.dT a = d.dT k ∧
      ∀ i, d.iDz i a = d.iDz (galoisColumn i) k) → k = b)
    (hneg : ∀ k, ¬ (d.dT a = -d.dT k ∧
      ∀ i, d.iDz i a = -d.iDz (galoisColumn i) k)) :
    degree a = degree b := by
  obtain ⟨σ, hs⟩ := h
  obtain ⟨ε, he, hd, ht, hz⟩ := hs a
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · have hk := hpos (σ a) ⟨by simpa using ht, by simpa using hz⟩
    simpa [hk] using hd
  · exact False.elim (hneg (σ a) ⟨by simpa using ht, by simpa using hz⟩)

private def cData (v : ZChoice) : GeneralizedDecompositionData (Fin 12) := tableIData .C v

private theorem c_t (v : ZChoice) (j : Fin 12) :
    (cData v).dT j = ![1, -1, -1, -1, -1, -2, 1, 1, 1, 2, 0, 0] j := by
  cases v <;> fin_cases j <;> decide

private theorem c_z (v : ZChoice) (j : Fin 12) :
    (cData v).zValue j = ![1, 3, 3, 3, 3, 10, 1, 5, 5, 10, 4, 4] j := by
  cases v <;> fin_cases j <;> decide

private theorem c_i0 (v : ZChoice) (j : Fin 12) :
    (cData v).iDz 0 j = ![1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 0, 0] j := by
  cases v <;> fin_cases j <;> decide

private theorem c_i1_z1 (j : Fin 12) :
    (cData .z1).iDz 1 j = ![0, 1, 1, 1, -1, 2, 0, 1, 1, 2, 1, 1] j := by
  fin_cases j <;> decide

private theorem c_i1_z2 (j : Fin 12) :
    (cData .z2).iDz 1 j = ![0, 0, 0, 0, 2, 2, 0, 1, 1, 2, 1, 1] j := by
  fin_cases j <;> decide

private theorem c_system (v : ZChoice) (degree : Fin 12 → ℤ)
    (hd : (tableIData .C v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .C v).OrderConstraints degree g c e) :
    degree 5 = -2 * degree 1 ∧
    0 < 72/(degree 1:ℚ) + 400/(degree 5:ℚ) ∧
    1+18/(degree 1:ℚ)+1/(degree 6:ℚ)-16/(degree 10:ℚ)-16/(degree 11:ℚ)=0 := by
  change (cData v).DegreeConstraints 0 degree at hd
  change (cData v).OrderConstraints degree g c e at ho
  have h12 := degree_step degree hd.galois_symmetry 1 2
    (by cases v <;> decide) (by cases v <;> decide)
  have h23 := degree_step degree hd.galois_symmetry 2 3
    (by cases v <;> decide) (by cases v <;> decide)
  have h34 := degree_step degree hd.galois_symmetry 3 4
    (by cases v <;> decide) (by cases v <;> decide)
  have ht := hd.orthogonal_t
  have hz := hd.orthogonal_z 0
  have hp := ho.weighted_z_sub_t_pos 0
  have heq := ho.equal_z 1
  have hpr : degree 0 = 1 := hd.principal_degree
  have hvec : degree = ![degree 0, degree 1, degree 2, degree 3, degree 4, degree 5, degree 6, degree 7, degree 8, degree 9, degree 10, degree 11] := by
    ext j
    fin_cases j <;> rfl
  cases v <;>
    simp only [columnInner, weightedColumn, c_t, c_z, c_i0, c_i1_z1, c_i1_z2,
      Fin.sum_univ_succ] at ht hz hp heq
  all_goals rw [hvec] at ht hz hp heq
  all_goals dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at ht hz hp heq
  all_goals norm_num [hpr, ← h34, ← h23, ← h12] at ht hz hp heq
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (solve | linarith)
    | (solve | linear_combination hp)
    | (linear_combination -heq)

/-- Case C is impossible from the signed degree and order constraints alone. This covers both Z₁/Z₂ variants. -/
theorem tableIC_impossible (v : ZChoice) (degree : Fin 12 → ℤ)
    (hd : (tableIData .C v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .C v).OrderConstraints degree g c e) : False := by
  obtain ⟨hrel, hpos, heq⟩ := c_system v degree hd ho
  change (cData v).DegreeConstraints 0 degree at hd
  have hs := hd.bounds_tneg2_z10 5 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy := hd.bounds_t1_z1 6 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hu := hd.bounds_t0_z4 10 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hv := hd.bounds_t0_z4 11 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hm := hd.multiplicity_integral 1
  norm_num [Int.ModEq, c_z, c_t] at hm
  have hxm : (degree 1 - 51) % 64 = 0 := by omega
  exact cef_arithmetic _ _ _ _ _ hs hy hu hv hxm hrel hpos heq

private def eData (v : ZChoice) : GeneralizedDecompositionData (Fin 15) := tableIData .E v

private theorem e_t (v : ZChoice) (j : Fin 15) :
    (eData v).dT j = ![1, -1, -1, -1, -1, -2, 1, 1, 1, 1, 1, 1, 1, 0, 0] j := by
  cases v <;> fin_cases j <;> decide

private theorem e_z (v : ZChoice) (j : Fin 15) :
    (eData v).zValue j = ![1, 3, 3, 3, 3, 10, 1, 5, 5, 5, 5, 5, 5, 4, 4] j := by
  cases v <;> fin_cases j <;> decide

private theorem e_i0 (v : ZChoice) (j : Fin 15) :
    (eData v).iDz 0 j = ![1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 0] j := by
  cases v <;> fin_cases j <;> decide

private theorem e_i1_z1 (j : Fin 15) :
    (eData .z1).iDz 1 j = ![0, 1, 1, 1, -1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1] j := by
  fin_cases j <;> decide

private theorem e_i1_z2 (j : Fin 15) :
    (eData .z2).iDz 1 j = ![0, 0, 0, 0, 2, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1] j := by
  fin_cases j <;> decide

private theorem e_system (v : ZChoice) (degree : Fin 15 → ℤ)
    (hd : (tableIData .E v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .E v).OrderConstraints degree g c e) :
    degree 5 = -2 * degree 1 ∧
    0 < 72/(degree 1:ℚ) + 400/(degree 5:ℚ) ∧
    1+18/(degree 1:ℚ)+1/(degree 6:ℚ)-16/(degree 13:ℚ)-16/(degree 14:ℚ)=0 := by
  change (eData v).DegreeConstraints 0 degree at hd
  change (eData v).OrderConstraints degree g c e at ho
  have h12 := degree_step degree hd.galois_symmetry 1 2
    (by cases v <;> decide) (by cases v <;> decide)
  have h23 := degree_step degree hd.galois_symmetry 2 3
    (by cases v <;> decide) (by cases v <;> decide)
  have h34 := degree_step degree hd.galois_symmetry 3 4
    (by cases v <;> decide) (by cases v <;> decide)
  have ht := hd.orthogonal_t
  have hz := hd.orthogonal_z 0
  have hp := ho.weighted_z_sub_t_pos 0
  have heq := ho.equal_z 1
  have hpr : degree 0 = 1 := hd.principal_degree
  have hvec : degree = ![degree 0, degree 1, degree 2, degree 3, degree 4, degree 5, degree 6, degree 7, degree 8, degree 9, degree 10, degree 11, degree 12, degree 13, degree 14] := by
    ext j
    fin_cases j <;> rfl
  cases v <;>
    simp only [columnInner, weightedColumn, e_t, e_z, e_i0, e_i1_z1, e_i1_z2,
      Fin.sum_univ_succ] at ht hz hp heq
  all_goals rw [hvec] at ht hz hp heq
  all_goals dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at ht hz hp heq
  all_goals norm_num [hpr, ← h34, ← h23, ← h12] at ht hz hp heq
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (solve | linarith)
    | (solve | linear_combination hp)
    | (linear_combination -heq)

/-- Case E is impossible from the signed degree and order constraints alone. This covers both Z₁/Z₂ variants. -/
theorem tableIE_impossible (v : ZChoice) (degree : Fin 15 → ℤ)
    (hd : (tableIData .E v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .E v).OrderConstraints degree g c e) : False := by
  obtain ⟨hrel, hpos, heq⟩ := e_system v degree hd ho
  change (eData v).DegreeConstraints 0 degree at hd
  have hs := hd.bounds_tneg2_z10 5 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy := hd.bounds_t1_z1 6 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hu := hd.bounds_t0_z4 13 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hv := hd.bounds_t0_z4 14 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hm := hd.multiplicity_integral 1
  norm_num [Int.ModEq, e_z, e_t] at hm
  have hxm : (degree 1 - 51) % 64 = 0 := by omega
  exact cef_arithmetic _ _ _ _ _ hs hy hu hv hxm hrel hpos heq

private def fData : GeneralizedDecompositionData (Fin 15) := tableIData .F ()

private theorem f_t (j : Fin 15) :
    (fData).dT j = ![1, 1, 1, 1, 1, -1, -1, -1, -1, -2, 1, 1, 1, 0, 0] j := by
  fin_cases j <;> decide

private theorem f_z (j : Fin 15) :
    (fData).zValue j = ![1, 5, 5, 5, 5, 3, 3, 3, 3, 10, 5, 5, 1, 4, 4] j := by
  fin_cases j <;> decide

private theorem f_i0 (j : Fin 15) :
    (fData).iDz 0 j = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 0] j := by
  fin_cases j <;> decide

private theorem f_i1 (j : Fin 15) :
    (fData).iDz 1 j = ![0, 2, 0, 1, 1, 1, 1, 0, 0, 2, 1, 1, 0, 1, 1] j := by
  fin_cases j <;> decide

private theorem f_system (degree : Fin 15 → ℤ)
    (hd : (tableIData .F ()).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .F ()).OrderConstraints degree g c e) :
    degree 9 = -2 * degree 5 ∧
    0 < 72/(degree 5:ℚ) + 400/(degree 9:ℚ) ∧
    1+18/(degree 5:ℚ)+1/(degree 12:ℚ)-16/(degree 13:ℚ)-16/(degree 14:ℚ)=0 := by
  change (fData).DegreeConstraints 0 degree at hd
  change (fData).OrderConstraints degree g c e at ho
  have h12 := degree_step degree hd.galois_symmetry 1 2
    (by decide) (by decide)
  have h23 := degree_step degree hd.galois_symmetry 2 3
    (by decide) (by decide)
  have h34 := degree_step degree hd.galois_symmetry 3 4
    (by decide) (by decide)
  have h56 := degree_step degree hd.galois_symmetry 5 6
    (by decide) (by decide)
  have h67 := degree_step degree hd.galois_symmetry 6 7
    (by decide) (by decide)
  have h78 := degree_step degree hd.galois_symmetry 7 8
    (by decide) (by decide)
  have ht := hd.orthogonal_t
  have hz := hd.orthogonal_z 0
  have hp := ho.weighted_z_sub_t_pos 0
  have heq := ho.equal_z 1
  have hpr : degree 0 = 1 := hd.principal_degree
  have hvec : degree = ![degree 0, degree 1, degree 2, degree 3, degree 4, degree 5, degree 6, degree 7, degree 8, degree 9, degree 10, degree 11, degree 12, degree 13, degree 14] := by
    ext j
    fin_cases j <;> rfl
  simp only [columnInner, weightedColumn, f_t, f_z, f_i0, f_i1,
      Fin.sum_univ_succ] at ht hz hp heq
  all_goals rw [hvec] at ht hz hp heq
  all_goals dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at ht hz hp heq
  all_goals norm_num [hpr, ← h78, ← h67, ← h56, ← h34, ← h23, ← h12] at ht hz hp heq
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (solve | linarith)
    | (solve | linear_combination hp)
    | (linear_combination -heq)

/-- Case F is impossible from the signed degree and order constraints alone. -/
theorem tableIF_impossible (degree : Fin 15 → ℤ)
    (hd : (tableIData .F ()).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (tableIData .F ()).OrderConstraints degree g c e) : False := by
  obtain ⟨hrel, hpos, heq⟩ := f_system degree hd ho
  change (fData).DegreeConstraints 0 degree at hd
  have hs := hd.bounds_tneg2_z10 9 (by decide) (by decide) (by decide)
  have hy := hd.bounds_t1_z1 12 (by decide) (by decide) (by decide)
  have hu := hd.bounds_t0_z4 13 (by decide) (by decide) (by decide)
  have hv := hd.bounds_t0_z4 14 (by decide) (by decide) (by decide)
  have hm := hd.multiplicity_integral 5
  norm_num [Int.ModEq, f_z, f_t] at hm
  change 64 ∣ degree 5 + 3 * 3 + 60 * (-1) at hm
  have hxm : (degree 5 - 51) % 64 = 0 := by omega
  exact cef_arithmetic _ _ _ _ _ hs hy hu hv hxm hrel hpos heq

/-- Uniform interface for the three eliminated cases and all their valid variants. -/
theorem tableICEF_impossible (c : TableICase) (v : c.Variant)
    (hc : c = .C ∨ c = .E ∨ c = .F)
    (degree : Fin (tableIRowCount c) → ℤ)
    (hd : (tableIData c v).DegreeConstraints (tableIPrincipal c) degree)
    {g a b : ℕ} (ho : (tableIData c v).OrderConstraints degree g a b) : False := by
  rcases hc with rfl | rfl | rfl
  · exact tableIC_impossible v degree hd ho
  · exact tableIE_impossible v degree hd ho
  · cases v
    exact tableIF_impossible degree hd ho

end Stellmacher.Recognition.LyonsU3Four
