module

public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIBArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

/-!
# Elimination of both variants of Table I case B

Signed Galois symmetry forces the first four nonprincipal degrees to agree.
Ordinary column orthogonality then gives `x₂ = -2x₁`, while the positive
weighted difference gives `-128/x₁ > 0`. Evaluating the remaining columns
produces Lyons's (B1)–(B4), with all degree bounds obtained from the signed
restriction multiplicity and its congruence modulo 64.

The arithmetic module leaves three configurations. Explicit row separation
and the prime constraint exclude them using `157 ∣ 471`, `59 ∣ 118`, and
`41 ∣ 41`, respectively. All eleven rows, including the two identical rows
labelled `y₁,y₂`, are retained; their degrees are not assumed equal.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Table I and pp. 382–383. The equations and signs were checked
against the page images of
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators
-- A fixed row type for evaluating the canonical catalogue; definitionally
-- equal to `tableIData .B v`, as used in the final theorem.
private def bData (v : TableICatalogue.ZChoice) : GeneralizedDecompositionData (Fin 11) where
  dT j := TableICatalogue.rowsB v j 0
  iDz i j := TableICatalogue.rowsB v j i.succ
private theorem degree_step (v : TableICatalogue.ZChoice) (degree : Fin 11 → ℤ)
    (h : (bData v).SignedGaloisSymmetry degree) (a b : Fin 11)
    (hpos : ∀ k : Fin 11, ((bData v).dT a = (bData v).dT k ∧
      ∀ i, (bData v).iDz i a = (bData v).iDz (galoisColumn i) k) → k = b)
    (hneg : ∀ k : Fin 11, ¬ ((bData v).dT a = -(bData v).dT k ∧
      ∀ i, (bData v).iDz i a = -(bData v).iDz (galoisColumn i) k)) :
    degree a = degree b := by
  obtain ⟨σ, hs⟩ := h
  obtain ⟨ε, he, hd, ht, hz⟩ := hs a
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · have hk := hpos (σ a) ⟨by simpa using ht, by simpa using hz⟩
    simpa [hk] using hd
  · exact False.elim (hneg (σ a) ⟨by simpa using ht, by simpa using hz⟩)

private theorem galois_degrees (v : TableICatalogue.ZChoice) (degree : Fin 11 → ℤ)
    (h : (bData v).SignedGaloisSymmetry degree) :
    degree 1 = degree 2 ∧ degree 2 = degree 3 ∧ degree 3 = degree 4 := by
  exact ⟨degree_step v degree h 1 2 (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide) (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide),
    degree_step v degree h 2 3 (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide) (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide),
    degree_step v degree h 3 4 (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide) (by cases v <;> dsimp [bData, TableICatalogue.rowsB] <;> decide)⟩
private theorem t_values (v : TableICatalogue.ZChoice) (j : Fin 11) :
    (bData v).dT j = ![1,-1,-1,-1,-1,-2,1,1,1,2,0] j := by
  cases v <;> fin_cases j <;> decide
private theorem z_values (v : TableICatalogue.ZChoice) (j : Fin 11) :
    (bData v).zValue j = ![1,3,3,3,3,10,5,5,9,6,4] j := by
  cases v <;> fin_cases j <;> decide
private theorem z0_values (v : TableICatalogue.ZChoice) (j : Fin 11) :
    (bData v).iDz 0 j = ![1,1,1,1,1,2,1,1,1,2,0] j := by
  cases v <;> fin_cases j <;> decide
private theorem z1_values (j : Fin 11) :
    (bData .z1).iDz 1 j = ![0,1,1,1,-1,2,1,1,2,1,1] j := by
  fin_cases j <;> decide
private theorem z2_values (j : Fin 11) :
    (bData .z2).iDz 1 j = ![0,0,0,0,2,2,1,1,2,1,1] j := by
  fin_cases j <;> decide

private theorem equations (v : TableICatalogue.ZChoice) (degree : Fin 11 → ℤ)
    (hd : (bData v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (bData v).OrderConstraints degree g c e) :
    degree 5 = -2*degree 1 ∧ degree 1 < 0 ∧
    (1+18/(degree 1:ℚ)-81/(degree 8:ℚ)+36/(degree 9:ℚ)-16/(degree 10:ℚ)=0) ∧
    (2+82/(degree 1:ℚ)+25/(degree 6:ℚ)+25/(degree 7:ℚ)+108/(degree 9:ℚ)-16/(degree 10:ℚ)=0) ∧
    (1+2*degree 1-degree 8+degree 9-degree 10=0) ∧
    (1+degree 6+degree 7+degree 8+2*degree 9=0) := by
  obtain ⟨h12,h23,h34⟩ := galois_degrees v degree hd.galois_symmetry
  have h0 := hd.principal_degree
  have ht := hd.orthogonal_t
  have hz := hd.orthogonal_z 0
  simp only [columnInner, t_values, z0_values, Fin.sum_univ_succ] at ht hz
  dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at ht hz
  norm_num [h0, ← h34, ← h23, ← h12] at ht hz
  change 1 + (-degree 1 + (-degree 2 + (-degree 3 + (-degree 4 +
    (-(degree 5*2) + (degree 6 + (degree 7 + (degree 8 + degree 9*2)))))))) = 0 at ht
  change 1 + (degree 1 + (degree 2 + (degree 3 + (degree 4 +
    (degree 5*2 + (degree 6 + (degree 7 + (degree 8 + degree 9*2)))))))) = 0 at hz
  rw [← h34, ← h23, ← h12] at ht hz
  have hx2 : degree 5 = -2*degree 1 := by linarith
  have h4 : 1+degree 6+degree 7+degree 8+2*degree 9=0 := by linarith
  have h3 : 1+2*degree 1-degree 8+degree 9-degree 10=0 := by
    have hz1 := hd.orthogonal_z 1
    cases v
    · simp only [columnInner, z1_values, Fin.sum_univ_succ] at hz1
      dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hz1
      norm_num at hz1
      change degree 1 + (degree 2 + (degree 3 + (-degree 4 +
        (degree 5*2 + (degree 6 + (degree 7 + (degree 8*2 + (degree 9 + degree 10)))))))) = 0 at hz1
      rw [← h34, ← h23, ← h12] at hz1
      linarith only [hz1, hz]
    · simp only [columnInner, z2_values, Fin.sum_univ_succ] at hz1
      dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hz1
      norm_num at hz1
      change degree 4*2 + (degree 5*2 + (degree 6 + (degree 7 +
        (degree 8*2 + (degree 9 + degree 10))))) = 0 at hz1
      rw [← h34, ← h23, ← h12] at hz1
      linarith only [hz1, hz]
  have hrecip : (400:ℚ)/(degree 5:ℚ) = -200/(degree 1:ℚ) := by
    rw [hx2]
    push_cast
    field_simp
    ring
  have hp := ho.weighted_z_sub_t_pos 0
  simp only [weightedColumn, z_values, z0_values, t_values, Fin.sum_univ_succ] at hp
  dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hp
  norm_num [h0, ← h34, ← h23, ← h12] at hp
  change 0 < 18/(degree 1:ℚ) + (18/(degree 2:ℚ) +
    (18/(degree 3:ℚ) + (18/(degree 4:ℚ) + 400/(degree 5:ℚ)))) at hp
  rw [← h34, ← h23, ← h12, hrecip] at hp
  have hp' : (0:ℚ) < -128/(degree 1:ℚ) := by
    convert hp using 1
    ring
  have hxneg : degree 1 < 0 := by
    by_contra hn
    have hxq : (0:ℚ) ≤ degree 1 := by exact_mod_cast (show 0 ≤ degree 1 by omega)
    have hq : (-128:ℚ)/(degree 1:ℚ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hxq
    exact (not_lt_of_ge hq) hp'
  have h1 : 1+18/(degree 1:ℚ)-81/(degree 8:ℚ)+36/(degree 9:ℚ)-16/(degree 10:ℚ)=0 := by
    have hh := ho.equal_z 1
    cases v
    · simp only [weightedColumn, z_values, z0_values, z1_values, Fin.sum_univ_succ] at hh
      dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hh
      norm_num [h0] at hh
      change 9/(degree 1:ℚ)+(9/(degree 2:ℚ)+(9/(degree 3:ℚ)+(-9/(degree 4:ℚ)+
        (200/(degree 5:ℚ)+(25/(degree 6:ℚ)+(25/(degree 7:ℚ)+(162/(degree 8:ℚ)+
        (36/(degree 9:ℚ)+16/(degree 10:ℚ))))))))) =
        1+(9/(degree 1:ℚ)+(9/(degree 2:ℚ)+(9/(degree 3:ℚ)+(9/(degree 4:ℚ)+
        (200/(degree 5:ℚ)+(25/(degree 6:ℚ)+(25/(degree 7:ℚ)+(81/(degree 8:ℚ)+72/(degree 9:ℚ))))))))) at hh
      rw [← h34, ← h23, ← h12] at hh
      linear_combination -hh
    · simp only [weightedColumn, z_values, z0_values, z2_values, Fin.sum_univ_succ] at hh
      dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hh
      norm_num [h0] at hh
      change 18/(degree 4:ℚ)+(200/(degree 5:ℚ)+(25/(degree 6:ℚ)+(25/(degree 7:ℚ)+
        (162/(degree 8:ℚ)+(36/(degree 9:ℚ)+16/(degree 10:ℚ)))))) =
        1+(9/(degree 1:ℚ)+(9/(degree 2:ℚ)+(9/(degree 3:ℚ)+(9/(degree 4:ℚ)+
        (200/(degree 5:ℚ)+(25/(degree 6:ℚ)+(25/(degree 7:ℚ)+(81/(degree 8:ℚ)+72/(degree 9:ℚ))))))))) at hh
      rw [← h34, ← h23, ← h12] at hh
      linear_combination -hh
  have h2 : 2+82/(degree 1:ℚ)+25/(degree 6:ℚ)+25/(degree 7:ℚ)+108/(degree 9:ℚ)-16/(degree 10:ℚ)=0 := by
    have hh := ho.zero_t
    simp only [weightedColumn, z_values, t_values, Fin.sum_univ_succ] at hh
    dsimp only [Matrix.vecCons, Fin.cases, Fin.succ] at hh
    norm_num [h0, ← h34, ← h23, ← h12, hx2] at hh
    change 1+(-9/(degree 1:ℚ)+(-9/(degree 2:ℚ)+(-9/(degree 3:ℚ)+(-9/(degree 4:ℚ)+
      (-200/(degree 5:ℚ)+(25/(degree 6:ℚ)+(25/(degree 7:ℚ)+(81/(degree 8:ℚ)+72/(degree 9:ℚ))))))))) = 0 at hh
    rw [← h34, ← h23, ← h12, hx2] at hh
    push_cast at hh
    linear_combination h1 + hh
  exact ⟨hx2,hxneg,h1,h2,h3,h4⟩
private theorem row_separated (v : TableICatalogue.ZChoice) (degree : Fin 11 → ℤ)
    (j : Fin 11) (hj : j = 1 ∨ j = 10) : (bData v).RowSeparated degree j := by
  have hpos : ∀ k : Fin 11, ((bData v).dT k = (bData v).dT j ∧
      ∀ i, (bData v).iDz i k = (bData v).iDz i j) → k = j := by
    rcases hj with rfl | rfl <;> cases v <;> decide
  have hneg : ∀ k : Fin 11, ¬ ((bData v).dT k = -(bData v).dT j ∧
      ∀ i, (bData v).iDz i k = -(bData v).iDz i j) := by
    rcases hj with rfl | rfl <;> cases v <;> decide
  intro k ε he _ ht hz
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · exact hpos k ⟨by simpa using ht, by simpa using hz⟩
  · exact False.elim (hneg k ⟨by simpa using ht, by simpa using hz⟩)

private theorem b_impossible (v : TableICatalogue.ZChoice) (degree : Fin 11 → ℤ)
    (hd : (bData v).DegreeConstraints 0 degree)
    {g c e : ℕ} (ho : (bData v).OrderConstraints degree g c e)
    (hp : (bData v).PrimeConstraints degree g) : False := by
  obtain ⟨hx2,hxn,h1,h2,h3,h4⟩ := equations v degree hd ho
  have hx2b := hd.bounds_tneg2_z10 5 (by decide) (by simp [t_values]) (by simp [z_values])
  have ha := hd.bounds_t1_z5 6 (by decide) (by simp [t_values]) (by simp [z_values])
  have hb := hd.bounds_t1_z5 7 (by decide) (by simp [t_values]) (by simp [z_values])
  have hc := hd.bounds_t1_z9 8 (by decide) (by simp [t_values]) (by simp [z_values])
  have hd' := hd.bounds_t2_z6 9 (by decide) (by simp [t_values]) (by simp [z_values])
  have he := hd.bounds_t0_z4 10 (by decide) (by simp [t_values]) (by simp [z_values])
  have hm (j : Fin 11) :
      (degree j + 3*(![1,3,3,3,3,10,5,5,9,6,4] j) +
        60*(![1,-1,-1,-1,-1,-2,1,1,1,2,0] j)) % 64 = 0 := by
    have hh := hd.multiplicity_integral j
    simpa [Int.ModEq, t_values, z_values] using hh
  have hxm : (degree 1-51)%64=0 := by
    have hh := hm 1
    change (degree 1+3*3+60*(-1))%64=0 at hh
    omega
  have ham : (degree 6-53)%64=0 := by
    have hh := hm 6
    change (degree 6+3*5+60*(1))%64=0 at hh
    omega
  have hbm : (degree 7-53)%64=0 := by
    have hh := hm 7
    change (degree 7+3*5+60*(1))%64=0 at hh
    omega
  have hcm : (degree 8-41)%64=0 := by
    have hh := hm 8
    change (degree 8+3*9+60*(1))%64=0 at hh
    omega
  have hdm : (degree 9-54)%64=0 := by
    have hh := hm 9
    change (degree 9+3*6+60*(2))%64=0 at hh
    omega
  have hem : (degree 10-52)%64=0 := by
    have hh := hm 10
    change (degree 10+3*4+60*(0))%64=0 at hh
    omega
  have hx : degree 1 ≤ -77 := by omega
  have hh := tableI_B_arithmetic (degree 1) (degree 6) (degree 7) (degree 8)
    (degree 9) (degree 10) hx ha hb hc hd' he hxm ham hbm hcm hdm hem h1 h2 h3 h4
  rcases hh with ⟨hx,hc⟩ | ⟨hd',he⟩ | ⟨hc,he⟩
  · have hh := hp.prime_dvd_degree_le (j := 1)
      (by rw [hx]; norm_num) (row_separated v degree 1 (Or.inl rfl)) 8
      (p := 157) (by norm_num) (by rw [hc]; norm_num)
    rw [hx] at hh
    norm_num at hh
  · have hh := hp.prime_dvd_degree_le (j := 10)
      (by rw [he]; norm_num) (row_separated v degree 10 (Or.inr rfl)) 9
      (p := 59) (by norm_num) (by rw [hd']; norm_num)
    rw [he] at hh
    norm_num at hh
  · have hh := hp.prime_dvd_degree_le (j := 10)
      (by rw [he]; norm_num) (row_separated v degree 10 (Or.inr rfl)) 8
      (p := 41) (by norm_num) (by rw [hc]; norm_num)
    rw [he] at hh
    norm_num at hh

/-- Neither of the two explicit case B matrices admits the signed degree,
positive order, and prime constraints. -/
theorem tableIB_impossible (v : TableICase.B.Variant)
    (degree : Fin (tableIRowCount .B) → ℤ)
    (hd : (tableIData .B v).DegreeConstraints (tableIPrincipal .B) degree)
    {g c e : ℕ} (ho : (tableIData .B v).OrderConstraints degree g c e)
    (hp : (tableIData .B v).PrimeConstraints degree g) : False :=
  b_impossible v degree hd ho hp

end Stellmacher.Recognition.LyonsU3Four
