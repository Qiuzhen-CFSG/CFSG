module

public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIADGArithmetic
import Mathlib.Tactic.LinearCombination

/-!
# Elimination of Table I cases A, D and G

The actual matrices give the common reciprocal and integral equations by
subtracting the second involution column from the first. Signed Galois
symmetry supplies the repeated degree labels; in G the relevant label is
in the second orbit. Signed multiplicity bounds and congruences feed one
arithmetic elimination. The degree-13 branch uses an explicit separated
row and the prime divisors 29, 151, 43 and 31 of the four small candidates.

Source: R. Lyons, A Characterization of the Group U₃(4), Trans. Amer. Math.
Soc. 164 (1972), pp. 382–383. Checked against the page images of
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators

private theorem degree_step {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    (degree : I → ℤ) (h : d.SignedGaloisSymmetry degree) (a b : I)
    (hpos : ∀ k, (d.dT a = d.dT k ∧ ∀ i, d.iDz i a = d.iDz (galoisColumn i) k) → k = b)
    (hneg : ∀ k, ¬ (d.dT a = -d.dT k ∧ ∀ i, d.iDz i a = -d.iDz (galoisColumn i) k)) :
    degree a = degree b := by
  obtain ⟨σ, hs⟩ := h
  obtain ⟨ε, he, hd, ht, hz⟩ := hs a
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · have hk := hpos (σ a) ⟨by simpa using ht, by simpa using hz⟩
    simpa [hk] using hd
  · exact False.elim (hneg (σ a) ⟨by simpa using ht, by simpa using hz⟩)

private theorem separated {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    (degree : I → ℤ) (j : I)
    (hpos : ∀ k, (d.dT k = d.dT j ∧ ∀ i, d.iDz i k = d.iDz i j) → k = j)
    (hneg : ∀ k, ¬ (d.dT k = -d.dT j ∧ ∀ i, d.iDz i k = -d.iDz i j)) :
    d.RowSeparated degree j := by
  intro k ε he _ ht hz
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · exact hpos k ⟨by simpa using ht, by simpa using hz⟩
  · exact False.elim (hneg k ⟨by simpa using ht, by simpa using hz⟩)

private theorem small_bound {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {degree : I → ℤ} {g : ℕ} (hp : d.PrimeConstraints degree g)
    (j k : I) (hj : d.RowSeparated degree j) (hx : degree j = -13)
    (hk : degree k ≤ -87 ∨ 41 ≤ degree k)
    (hm : (degree k-41)%64=0) (hn : degree k < 0) : degree k ≤ -343 := by
  by_contra hh
  have casesK : degree k = -87 ∨ degree k = -151 ∨ degree k = -215 ∨ degree k = -279 := by omega
  have hb : ∀ p : ℕ, p.Prime → p ∣ (degree k).natAbs → p ≤ 14 := by
    intro p hpp hpk
    have := hp.prime_dvd_degree_le (j := j) (by rw [hx]; decide) hj k hpp hpk
    simpa [hx] using this
  rcases casesK with he | he | he | he
  · have := hb 29 (by decide) (by rw [he]; decide); omega
  · have := hb 151 (by decide) (by rw [he]; decide); omega
  · have := hb 43 (by decide) (by rw [he]; decide); omega
  · have := hb 31 (by decide) (by rw [he]; decide); omega

private def dataA (v : TableICatalogue.ZChoice) : GeneralizedDecompositionData (Fin 10) where
  dT j := TableICatalogue.rowsA v j 0
  iDz i j := TableICatalogue.rowsA v j i.succ
private theorem A_galois (v : TableICatalogue.ZChoice) (degree : Fin 10 → ℤ)
    (h : (dataA v).SignedGaloisSymmetry degree) :
    degree 1 = degree 2 ∧ degree 2 = degree 3 ∧ degree 3 = degree 4 := by
  exact ⟨degree_step degree h 1 2 (by cases v <;> decide) (by cases v <;> decide),
    degree_step degree h 2 3 (by cases v <;> decide) (by cases v <;> decide),
    degree_step degree h 3 4 (by cases v <;> decide) (by cases v <;> decide)⟩

private theorem A_sep (v : TableICatalogue.ZChoice) (degree : Fin 10 → ℤ) :
    (dataA v).RowSeparated degree 1 :=
  separated degree 1 (by cases v <;> decide) (by cases v <;> decide)

private theorem A_zdiff (v : TableICatalogue.ZChoice) (j : Fin 10) :
    (dataA v).iDz 0 j - (dataA v).iDz 1 j =
    (match v with | .z1 => ![1,0,0,0,2,0,1,1,-1,0] | .z2 => ![1,1,1,1,-1,0,1,1,-1,0]) j := by
  cases v <;> fin_cases j <;> decide
private theorem A_zval (v : TableICatalogue.ZChoice) (j : Fin 10) :
    (dataA v).zValue j = ![1,3,3,3,3,10,1,1,9,10] j := by
  cases v <;> fin_cases j <;> decide

private theorem A_equations (v : TableICatalogue.ZChoice) (degree : Fin 10 → ℤ)
    (hd : (dataA v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (dataA v).OrderConstraints degree g c e) :
    (1+18/(degree 1:ℚ)+1/(degree 6:ℚ)+1/(degree 7:ℚ)-81/(degree 8:ℚ)=0) ∧
    (1+2*degree 1+degree 6+degree 7-degree 8=0) := by
  obtain ⟨h12,h23,h34⟩ := A_galois v degree hd.galois_symmetry
  have h1 : (dataA v).weightedColumn degree (fun j =>
      (dataA v).iDz 0 j - (dataA v).iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 : columnInner degree (fun j =>
      (dataA v).iDz 0 j - (dataA v).iDz 1 j) = 0 := by
    simp only [columnInner, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hd.orthogonal_z 0).trans (hd.orthogonal_z 1).symm)
  simp only [weightedColumn, A_zval, A_zdiff, Fin.sum_univ_succ] at h1
  simp only [columnInner, A_zdiff, Fin.sum_univ_succ] at h2
  cases v <;> dsimp at h1 h2
  all_goals
    have h0 : degree 0 = 1 := hd.principal_degree
    rw [h0, ← h34, ← h23, ← h12] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2

/-- The explicit case A matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableIA_impossible (v : TableICatalogue.ZChoice) (degree : Fin (tableIRowCount .A) → ℤ)
    (hd : (tableIData .A v).DegreeConstraints (tableIPrincipal .A) degree)
    {g c e : ℕ} (ho : (tableIData .A v).OrderConstraints degree g c e)
    (hp : (tableIData .A v).PrimeConstraints degree g) : False := by
  change (dataA v).DegreeConstraints 0 degree at hd
  change (dataA v).OrderConstraints degree g c e at ho
  change (dataA v).PrimeConstraints degree g at hp
  obtain ⟨h1,h2⟩ := A_equations v degree hd ho
  have hx := hd.bounds_tneg1_z3 1 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy₁ := hd.bounds_t1_z1 6 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy₂ := hd.bounds_t1_z1 7 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hz := hd.bounds_t1_z9 8 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hmX := hd.multiplicity_integral 1
  have hmZ := hd.multiplicity_integral 8
  have hmx : (degree 1-51)%64=0 := by
    cases v <;> change (degree 1+3*3+60*(-1))%64=0 at hmX
    all_goals omega
  have hmz : (degree 8-41)%64=0 := by
    cases v <;> change (degree 8+3*9+60*1)%64=0 at hmZ
    all_goals omega
  exact tableI_ADG_arithmetic _ _ _ _ hx hy₁ hy₂ hz hmx hmz
    (fun he hn => small_bound hp 1 8 (A_sep v degree) he hz hmz hn) h1 h2

private def dataD (v : TableICatalogue.ZChoice) : GeneralizedDecompositionData (Fin 13) where
  dT j := TableICatalogue.rowsD v j 0
  iDz i j := TableICatalogue.rowsD v j i.succ
private theorem D_galois (v : TableICatalogue.ZChoice) (degree : Fin 13 → ℤ)
    (h : (dataD v).SignedGaloisSymmetry degree) :
    degree 1 = degree 2 ∧ degree 2 = degree 3 ∧ degree 3 = degree 4 := by
  exact ⟨degree_step degree h 1 2 (by cases v <;> decide) (by cases v <;> decide),
    degree_step degree h 2 3 (by cases v <;> decide) (by cases v <;> decide),
    degree_step degree h 3 4 (by cases v <;> decide) (by cases v <;> decide)⟩

private theorem D_sep (v : TableICatalogue.ZChoice) (degree : Fin 13 → ℤ) :
    (dataD v).RowSeparated degree 1 :=
  separated degree 1 (by cases v <;> decide) (by cases v <;> decide)

private theorem D_zdiff (v : TableICatalogue.ZChoice) (j : Fin 13) :
    (dataD v).iDz 0 j - (dataD v).iDz 1 j =
    (match v with | .z1 => ![1,0,0,0,2,0,1,1,0,0,0,0,-1] | .z2 => ![1,1,1,1,-1,0,1,1,0,0,0,0,-1]) j := by
  cases v <;> fin_cases j <;> decide
private theorem D_zval (v : TableICatalogue.ZChoice) (j : Fin 13) :
    (dataD v).zValue j = ![1,3,3,3,3,10,1,1,5,5,5,5,9] j := by
  cases v <;> fin_cases j <;> decide

private theorem D_equations (v : TableICatalogue.ZChoice) (degree : Fin 13 → ℤ)
    (hd : (dataD v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (dataD v).OrderConstraints degree g c e) :
    (1+18/(degree 1:ℚ)+1/(degree 6:ℚ)+1/(degree 7:ℚ)-81/(degree 12:ℚ)=0) ∧
    (1+2*degree 1+degree 6+degree 7-degree 12=0) := by
  obtain ⟨h12,h23,h34⟩ := D_galois v degree hd.galois_symmetry
  have h1 : (dataD v).weightedColumn degree (fun j =>
      (dataD v).iDz 0 j - (dataD v).iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 : columnInner degree (fun j =>
      (dataD v).iDz 0 j - (dataD v).iDz 1 j) = 0 := by
    simp only [columnInner, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hd.orthogonal_z 0).trans (hd.orthogonal_z 1).symm)
  simp only [weightedColumn, D_zval, D_zdiff, Fin.sum_univ_succ] at h1
  simp only [columnInner, D_zdiff, Fin.sum_univ_succ] at h2
  cases v <;> dsimp at h1 h2
  all_goals
    have h0 : degree 0 = 1 := hd.principal_degree
    rw [h0, ← h34, ← h23, ← h12] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2

/-- The explicit case D matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableID_impossible (v : TableICatalogue.ZChoice) (degree : Fin (tableIRowCount .D) → ℤ)
    (hd : (tableIData .D v).DegreeConstraints (tableIPrincipal .D) degree)
    {g c e : ℕ} (ho : (tableIData .D v).OrderConstraints degree g c e)
    (hp : (tableIData .D v).PrimeConstraints degree g) : False := by
  change (dataD v).DegreeConstraints 0 degree at hd
  change (dataD v).OrderConstraints degree g c e at ho
  change (dataD v).PrimeConstraints degree g at hp
  obtain ⟨h1,h2⟩ := D_equations v degree hd ho
  have hx := hd.bounds_tneg1_z3 1 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy₁ := hd.bounds_t1_z1 6 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hy₂ := hd.bounds_t1_z1 7 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hz := hd.bounds_t1_z9 12 (by decide) (by cases v <;> decide) (by cases v <;> decide)
  have hmX := hd.multiplicity_integral 1
  have hmZ := hd.multiplicity_integral 12
  have hmx : (degree 1-51)%64=0 := by
    cases v <;> change (degree 1+3*3+60*(-1))%64=0 at hmX
    all_goals omega
  have hmz : (degree 12-41)%64=0 := by
    cases v <;> change (degree 12+3*9+60*1)%64=0 at hmZ
    all_goals omega
  exact tableI_ADG_arithmetic _ _ _ _ hx hy₁ hy₂ hz hmx hmz
    (fun he hn => small_bound hp 1 12 (D_sep v degree) he hz hmz hn) h1 h2

private def dataG : GeneralizedDecompositionData (Fin 13) where
  dT j := TableICatalogue.rowsG j 0
  iDz i j := TableICatalogue.rowsG j i.succ
private theorem G_galois (degree : Fin 13 → ℤ)
    (h : (dataG).SignedGaloisSymmetry degree) :
    degree 1 = degree 2 ∧ degree 2 = degree 3 ∧ degree 3 = degree 4 ∧ degree 5 = degree 6 ∧ degree 6 = degree 7 ∧ degree 7 = degree 8 := by
  exact ⟨degree_step degree h 1 2 (by decide) (by decide),
    degree_step degree h 2 3 (by decide) (by decide),
    degree_step degree h 3 4 (by decide) (by decide),
    degree_step degree h 5 6 (by decide) (by decide),
    degree_step degree h 6 7 (by decide) (by decide),
    degree_step degree h 7 8 (by decide) (by decide)⟩

private theorem G_sep (degree : Fin 13 → ℤ) :
    (dataG).RowSeparated degree 5 :=
  separated degree 5 (by decide) (by decide)

private theorem G_zdiff (j : Fin 13) :
    (dataG).iDz 0 j - (dataG).iDz 1 j =
    ![1,-1,1,0,0,0,0,1,1,0,-1,1,1] j := by
  fin_cases j <;> decide
private theorem G_zval (j : Fin 13) :
    (dataG).zValue j = ![1,5,5,5,5,3,3,3,3,10,9,1,1] j := by
  fin_cases j <;> decide

private theorem G_equations (degree : Fin 13 → ℤ)
    (hd : (dataG).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (dataG).OrderConstraints degree g c e) :
    (1+18/(degree 5:ℚ)+1/(degree 11:ℚ)+1/(degree 12:ℚ)-81/(degree 10:ℚ)=0) ∧
    (1+2*degree 5+degree 11+degree 12-degree 10=0) := by
  obtain ⟨h12,h23,h34,h56,h67,h78⟩ := G_galois degree hd.galois_symmetry
  have h1 : (dataG).weightedColumn degree (fun j =>
      (dataG).iDz 0 j - (dataG).iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 : columnInner degree (fun j =>
      (dataG).iDz 0 j - (dataG).iDz 1 j) = 0 := by
    simp only [columnInner, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hd.orthogonal_z 0).trans (hd.orthogonal_z 1).symm)
  simp only [weightedColumn, G_zval, G_zdiff, Fin.sum_univ_succ] at h1
  simp only [columnInner, G_zdiff, Fin.sum_univ_succ] at h2
  dsimp at h1 h2
  all_goals
    have h0 : degree 0 = 1 := hd.principal_degree
    rw [h0, ← h34, ← h23, ← h12, ← h78, ← h67, ← h56] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2

/-- The explicit case G matrix admits no simultaneous degree, order and prime constraints. -/
theorem tableIG_impossible (degree : Fin (tableIRowCount .G) → ℤ)
    (hd : (tableIData .G ()).DegreeConstraints (tableIPrincipal .G) degree)
    {g c e : ℕ} (ho : (tableIData .G ()).OrderConstraints degree g c e)
    (hp : (tableIData .G ()).PrimeConstraints degree g) : False := by
  change (dataG).DegreeConstraints 0 degree at hd
  change (dataG).OrderConstraints degree g c e at ho
  change (dataG).PrimeConstraints degree g at hp
  obtain ⟨h1,h2⟩ := G_equations degree hd ho
  have hx := hd.bounds_tneg1_z3 5 (by decide) (by decide) (by decide)
  have hy₁ := hd.bounds_t1_z1 11 (by decide) (by decide) (by decide)
  have hy₂ := hd.bounds_t1_z1 12 (by decide) (by decide) (by decide)
  have hz := hd.bounds_t1_z9 10 (by decide) (by decide) (by decide)
  have hmX := hd.multiplicity_integral 5
  have hmZ := hd.multiplicity_integral 10
  have hmx : (degree 5-51)%64=0 := by
    change (degree 5+3*3+60*(-1))%64=0 at hmX
    all_goals omega
  have hmz : (degree 10-41)%64=0 := by
    change (degree 10+3*9+60*1)%64=0 at hmZ
    all_goals omega
  exact tableI_ADG_arithmetic _ _ _ _ hx hy₁ hy₂ hz hmx hmz
    (fun he hn => small_bound hp 5 10 (G_sep degree) he hz hmz hn) h1 h2

end Stellmacher.Recognition.LyonsU3Four
