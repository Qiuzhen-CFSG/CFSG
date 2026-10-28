module

public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIGaloisNormalization
import Mathlib.Tactic.LinearCombination

/-!
# Matrix equations and degree normalization for Table I cases J, K and L

Galois normalization aligns the repeated degree labels without identifying
unrelated copies of equal rows. Expanding the actual catalogue matrices then
gives equations (J1)–(J3), (K1)–(K2), and (L1)–(L4), together with the
positive weighted combination used in J. Signed multiplicity and congruence
give the degree gaps. Row separation in K and L requires distinct degrees
on the identical rows; it does not follow from their printed labels.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
Table I pp. 375–376 and the elimination pp. 383–384. The page images were
checked in `refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
We use the catalogue's documented correction of J's row 9 to `dᵗ = -2`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators

private theorem separated_unique {I : Type*} [Fintype I]
    {d : GeneralizedDecompositionData I} (r : I → ℤ) (j : I)
    (hpos : ∀ k, (d.dT k = d.dT j ∧ ∀ i, d.iDz i k = d.iDz i j) → k = j)
    (hneg : ∀ k, ¬ (d.dT k = -d.dT j ∧ ∀ i, d.iDz i k = -d.iDz i j)) :
    d.RowSeparated r j := by
  intro k ε he _ ht hz
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · exact hpos k ⟨by simpa using ht, by simpa using hz⟩
  · exact False.elim (hneg k ⟨by simpa using ht, by simpa using hz⟩)

private theorem separated_except {I : Type*} [Fintype I]
    {d : GeneralizedDecompositionData I} (r : I → ℤ) (j other : I)
    (hpos : ∀ k, (d.dT k = d.dT j ∧ ∀ i, d.iDz i k = d.iDz i j) →
      k = j ∨ k = other)
    (hneg : ∀ k, ¬ (d.dT k = -d.dT j ∧ ∀ i, d.iDz i k = -d.iDz i j))
    (hne : r other ≠ r j) : d.RowSeparated r j := by
  intro k ε he hr ht hz
  rcases sq_eq_one_iff.mp he with rfl | rfl
  · rcases hpos k ⟨by simpa using ht, by simpa using hz⟩ with hk | hk
    · exact hk
    · subst k
      exact False.elim (hne (by simpa using hr))
  · exact False.elim (hneg k ⟨by simpa using ht, by simpa using hz⟩)

namespace EarlyJ

/-! Coordinates `x 2, x 3, x 4, x 7, x 8` are the printed `y₁, y₂, y₃, y₆, y₇`. -/

abbrev data : GeneralizedDecompositionData (Fin 14) := tableIData .J ()

/-- Labels zero and one are the principal and four-row orbit degrees;
labels two and three are the two printed two-row orbit degrees. -/
def label : Fin 14 → Fin 9 := ![0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8]
def representative : Fin 9 → Fin 14 := ![0, 1, 5, 7, 9, 10, 11, 12, 13]
def degree (x : Fin 9 → ℤ) : Fin 14 → ℤ := fun j => x (label j)
def offset : Fin 9 → ℤ := ![63, 75, -51, -39, -102, 75, 75, 63, 12]
def lower : Fin 9 → ℤ := ![-63, -75, -13, -25, -26, -75, -75, -63, -12]
def upper : Fin 9 → ℤ := ![65, 53, 51, 39, 102, 53, 53, 65, 52]

/-- A certificate of the printed Galois labels, preserving equal-row multiplicities. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 9) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Derive the printed labels from signed Galois symmetry, transporting all constraints. -/
theorem normalize_degree {r : Fin 14 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r) (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 9 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧ data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

theorem degree_representative (x : Fin 9 → ℤ) (i : Fin 9) :
    degree x (representative i) = x i := by fin_cases i <;> rfl

theorem degree_nonzero {x : Fin 9 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 9) : x i ≠ 0 := by
  simpa only [degree_representative] using h.degree_nonzero (representative i)

/-- The residue is computed from the signed row, including its t entry. -/
theorem degree_mod {x : Fin 9 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 9) : (x i + offset i) % 64 = 0 := by
  have hm := h.multiplicity_integral (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simpa only [degree_representative, add_assoc, hb, Int.ModEq, Int.zero_emod] using hm

/-- Gaps about zero use both signed multiplicity and the nonprincipal lower bound. -/
theorem degree_bounds {x : Fin 9 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 9) (hi : i ≠ 0) : x i ≤ lower i ∨ upper i ≤ x i := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hm := degree_mod h i
  have hl := h.degree_lower (representative i) hn
  have hs := h.multiplicity_nonneg (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simp only [degree_representative, add_assoc, hb] at hl hs
  fin_cases i <;> norm_num [lower, upper, offset] at hm hl hs ⊢
  all_goals rcases mul_nonneg_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

theorem degree_dvd {x : Fin 9 → ℤ} {g : ℕ}
    (h : data.PrimeConstraints (degree x) g) (i : Fin 9) : (x i).natAbs ∣ g := by
  simpa only [degree_representative] using h.degree_dvd (representative i)

private theorem z_values : data.zValue = ![1, 5, 5, 5, 5, 3, 3, 7, 7, 6, 5, 5, 1, 4] := by
  funext j
  fin_cases j <;> decide

private theorem t_values : data.dT = ![1, 1, 1, 1, 1, -1, -1, -1, -1, -2, 1, 1, 1, 0] := by
  funext j
  fin_cases j <;> decide

private theorem i0_values : data.iDz 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0] := by
  funext j
  fin_cases j <;> decide

private theorem i1_values : data.iDz 1 = ![0, 2, 1, 0, 1, 0, 1, 2, 1, 1, 1, 1, 0, 1] := by
  funext j
  fin_cases j <;> decide

/-- The equations extracted from the actual matrix, in normalized coordinates. -/
structure Equations (x : Fin 9 → ℤ) : Prop where
  h₁ : 1 + 9/(x 2 : ℚ) - 49/(x 3 : ℚ) + 36/(x 4 : ℚ) +
    1/(x 7 : ℚ) - 16/(x 8 : ℚ) = 0
  h₂ : 1 + x 2 - x 3 + x 4 + x 7 - x 8 = 0
  h₃ : x 2 + x 3 + x 4 = 0
  positive : 0 < -1 + 98/(x 3 : ℚ) - 1/(x 7 : ℚ) + 16/(x 8 : ℚ)

/-- Column differences give the displayed equations; positive orders give the strict bound. -/
theorem equations {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : Equations x := by
  have h0 : x 0 = 1 := hd.principal_degree
  have h1 : data.weightedColumn (degree x) (fun j => data.iDz 0 j - data.iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 := hd.orthogonal_z 0
  have h2' := hd.orthogonal_z 1
  have h3 := hd.orthogonal_t
  have hp := ho.weighted_z_sub_t_pos 0
  simp only [weightedColumn, columnInner] at h1 h2 h2' h3 hp
  rw [z_values, i0_values, i1_values] at h1
  rw [i0_values] at h2
  rw [i1_values] at h2'
  rw [t_values] at h3
  rw [z_values, i0_values, t_values] at hp
  change (∑ j : Fin 14, _) = 0 at h1 h2 h2' h3
  change 0 < (∑ j : Fin 14, _) at hp
  norm_num [degree, label, Fin.sum_univ_succ, h0] at h1 h2 h2' h3 hp
  constructor
  · linear_combination h1
  · omega
  · omega
  · simp only [div_eq_mul_inv, one_mul] at *
    linarith only [hp, h1]

/-- The degrees used in J's Schur argument occur in separated rows.
The row with label seven is separated from the principal row by its degree. -/
theorem row_separated {x : Fin 9 → ℤ} (hd : data.DegreeConstraints 0 (degree x))
    (i : Fin 9) (hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 8) :
    data.RowSeparated (degree x) (representative i) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact separated_unique _ _ (by decide) (by decide)
  · exact separated_unique _ _ (by decide) (by decide)
  · exact separated_unique _ _ (by decide) (by decide)
  · apply separated_except (degree x) (representative 7) 0 (by decide) (by decide)
    have h0 : x 0 = 1 := hd.principal_degree
    have hb := degree_bounds hd 7 (by decide)
    change x 7 ≤ -63 ∨ 65 ≤ x 7 at hb
    change x 0 ≠ x 7
    omega
  · exact separated_unique _ _ (by decide) (by decide)

/-- Schur's prime bound for each degree needed in J's elimination. -/
theorem prime_bound {x : Fin 9 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (hp : data.PrimeConstraints (degree x) g)
    (i : Fin 9) (hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 8)
    (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ (x i).natAbs + 1 := by
  have hn : representative i ≠ 0 := by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  have hl := hd.degree_lower (representative i) hn
  have hh := hp.prime_bound (representative i) (by omega)
    (row_separated hd i hi) p hpp hpg
  simpa only [degree_representative] using hh

end EarlyJ

namespace EarlyK

/-! Coordinates `x 2, x 3, x 5, x 6, x 7` are the printed `y₁, y₂, y₄, y₅, y₆`; `x 4` is the degree on row 9. -/

abbrev data : GeneralizedDecompositionData (Fin 13) := tableIData .K ()

/-- Labels zero and one are the principal and four-row orbit degrees;
labels two and three are the two printed two-row orbit degrees. -/
def label : Fin 13 → Fin 8 := ![0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7]
def representative : Fin 8 → Fin 13 := ![0, 1, 5, 7, 9, 10, 11, 12]
def degree (x : Fin 8 → ℤ) : Fin 13 → ℤ := fun j => x (label j)
def offset : Fin 8 → ℤ := ![63, 75, -51, -51, -90, 87, 63, 63]
def lower : Fin 8 → ℤ := ![-63, -75, -13, -13, -38, -87, -63, -63]
def upper : Fin 8 → ℤ := ![65, 53, 51, 51, 90, 41, 65, 65]

/-- A certificate of the printed Galois labels, preserving equal-row multiplicities. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 8) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Derive the printed labels from signed Galois symmetry, transporting all constraints. -/
theorem normalize_degree {r : Fin 13 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r) (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 8 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧ data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

theorem degree_representative (x : Fin 8 → ℤ) (i : Fin 8) :
    degree x (representative i) = x i := by fin_cases i <;> rfl

theorem degree_nonzero {x : Fin 8 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 8) : x i ≠ 0 := by
  simpa only [degree_representative] using h.degree_nonzero (representative i)

/-- The residue is computed from the signed row, including its t entry. -/
theorem degree_mod {x : Fin 8 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 8) : (x i + offset i) % 64 = 0 := by
  have hm := h.multiplicity_integral (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simpa only [degree_representative, add_assoc, hb, Int.ModEq, Int.zero_emod] using hm

/-- Gaps about zero use both signed multiplicity and the nonprincipal lower bound. -/
theorem degree_bounds {x : Fin 8 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 8) (hi : i ≠ 0) : x i ≤ lower i ∨ upper i ≤ x i := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hm := degree_mod h i
  have hl := h.degree_lower (representative i) hn
  have hs := h.multiplicity_nonneg (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simp only [degree_representative, add_assoc, hb] at hl hs
  fin_cases i <;> norm_num [lower, upper, offset] at hm hl hs ⊢
  all_goals rcases mul_nonneg_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

theorem degree_dvd {x : Fin 8 → ℤ} {g : ℕ}
    (h : data.PrimeConstraints (degree x) g) (i : Fin 8) : (x i).natAbs ∣ g := by
  simpa only [degree_representative] using h.degree_dvd (representative i)

private theorem z_values : data.zValue = ![1, 5, 5, 5, 5, 3, 3, 3, 3, 10, 9, 1, 1] := by
  funext j
  fin_cases j <;> decide

private theorem t_values : data.dT = ![1, 1, 1, 1, 1, -1, -1, -1, -1, -2, 1, 1, 1] := by
  funext j
  fin_cases j <;> decide

private theorem i0_values : data.iDz 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1] := by
  funext j
  fin_cases j <;> decide

private theorem i1_values : data.iDz 1 = ![0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 2, 0, 0] := by
  funext j
  fin_cases j <;> decide

/-- The equations extracted from the actual matrix, in normalized coordinates. -/
structure Equations (x : Fin 8 → ℤ) : Prop where
  h₁ : 1 + 9/(x 2 : ℚ) + 9/(x 3 : ℚ) - 81/(x 5 : ℚ) +
    1/(x 6 : ℚ) + 1/(x 7 : ℚ) = 0
  h₂ : 1 + x 2 + x 3 - x 5 + x 6 + x 7 = 0
  orbit_sum : x 2 + x 3 + x 4 = 0

/-- Column differences give the displayed equations; positive orders give the strict bound. -/
theorem equations {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : Equations x := by
  have h0 : x 0 = 1 := hd.principal_degree
  have h1 : data.weightedColumn (degree x) (fun j => data.iDz 0 j - data.iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 := hd.orthogonal_z 0
  have h2' := hd.orthogonal_z 1
  have h3 := hd.orthogonal_t
  simp only [weightedColumn, columnInner] at h1 h2 h2' h3
  rw [z_values, i0_values, i1_values] at h1
  rw [i0_values] at h2
  rw [i1_values] at h2'
  rw [t_values] at h3
  change (∑ j : Fin 13, _) = 0 at h1 h2 h2' h3
  norm_num [degree, label, Fin.sum_univ_succ, h0] at h1 h2 h2' h3
  constructor
  · linear_combination h1
  · omega
  · omega

/-- The printed row with label two is separated only after separating the two degrees. -/
theorem row_separated_two {x : Fin 8 → ℤ} (hne : x 2 ≠ x 3) :
    data.RowSeparated (degree x) 5 := by
  apply separated_except (degree x) 5 7 (by decide) (by decide)
  exact Ne.symm hne

/-- The degree-13 prime bound uses the proved separation, not the printed label. -/
theorem prime_bound_two {x : Fin 8 → ℤ} {g : ℕ}
    (hp : data.PrimeConstraints (degree x) g) (hne : x 2 ≠ x 3)
    (hx : x 2 = -13) (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ 14 := by
  have hr : degree x 5 = -13 := hx
  have hb := hp.prime_bound 5 (by rw [hr]; decide)
    (row_separated_two hne) p hpp hpg
  simpa [hr] using hb

/-- The printed row with label three is separated only after separating the two degrees. -/
theorem row_separated_three {x : Fin 8 → ℤ} (hne : x 2 ≠ x 3) :
    data.RowSeparated (degree x) 7 := by
  apply separated_except (degree x) 7 5 (by decide) (by decide)
  exact hne

/-- The degree-13 prime bound uses the proved separation, not the printed label. -/
theorem prime_bound_three {x : Fin 8 → ℤ} {g : ℕ}
    (hp : data.PrimeConstraints (degree x) g) (hne : x 2 ≠ x 3)
    (hx : x 3 = -13) (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ 14 := by
  have hr : degree x 7 = -13 := hx
  have hb := hp.prime_bound 7 (by rw [hr]; decide)
    (row_separated_three hne) p hpp hpg
  simpa [hr] using hb


end EarlyK

namespace EarlyL

/-! Coordinates `x 2, x 3, x 4, x 7, x 8, x 9` are the printed `y₁, y₂, y₃, y₆, y₇, y₈`. -/

abbrev data : GeneralizedDecompositionData (Fin 15) := tableIData .L ()

/-- Labels zero and one are the principal and four-row orbit degrees;
labels two and three are the two printed two-row orbit degrees. -/
def label : Fin 15 → Fin 10 := ![0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8, 9]
def representative : Fin 10 → Fin 15 := ![0, 1, 5, 7, 9, 10, 11, 12, 13, 14]
def degree (x : Fin 10 → ℤ) : Fin 15 → ℤ := fun j => x (label j)
def offset : Fin 10 → ℤ := ![63, 75, -51, -51, -90, 75, 75, 63, 12, 12]
def lower : Fin 10 → ℤ := ![-63, -75, -13, -13, -38, -75, -75, -63, -12, -12]
def upper : Fin 10 → ℤ := ![65, 53, 51, 51, 90, 53, 53, 65, 52, 52]

/-- A certificate of the printed Galois labels, preserving equal-row multiplicities. -/
def galoisLabeling : data.GaloisLabeling 0 (Fin 10) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

/-- Derive the printed labels from signed Galois symmetry, transporting all constraints. -/
theorem normalize_degree {r : Fin 15 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r) (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 10 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧ data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

theorem degree_representative (x : Fin 10 → ℤ) (i : Fin 10) :
    degree x (representative i) = x i := by fin_cases i <;> rfl

theorem degree_nonzero {x : Fin 10 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 10) : x i ≠ 0 := by
  simpa only [degree_representative] using h.degree_nonzero (representative i)

/-- The residue is computed from the signed row, including its t entry. -/
theorem degree_mod {x : Fin 10 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 10) : (x i + offset i) % 64 = 0 := by
  have hm := h.multiplicity_integral (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simpa only [degree_representative, add_assoc, hb, Int.ModEq, Int.zero_emod] using hm

/-- Gaps about zero use both signed multiplicity and the nonprincipal lower bound. -/
theorem degree_bounds {x : Fin 10 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 10) (hi : i ≠ 0) : x i ≤ lower i ∨ upper i ≤ x i := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hm := degree_mod h i
  have hl := h.degree_lower (representative i) hn
  have hs := h.multiplicity_nonneg (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) =
      offset i := by fin_cases i <;> decide
  simp only [degree_representative, add_assoc, hb] at hl hs
  fin_cases i <;> norm_num [lower, upper, offset] at hm hl hs ⊢
  all_goals rcases mul_nonneg_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

theorem degree_dvd {x : Fin 10 → ℤ} {g : ℕ}
    (h : data.PrimeConstraints (degree x) g) (i : Fin 10) : (x i).natAbs ∣ g := by
  simpa only [degree_representative] using h.degree_dvd (representative i)

private theorem z_values : data.zValue = ![1, 5, 5, 5, 5, 3, 3, 3, 3, 10, 5, 5, 1, 4, 4] := by
  funext j
  fin_cases j <;> decide

private theorem t_values : data.dT = ![1, 1, 1, 1, 1, -1, -1, -1, -1, -2, 1, 1, 1, 0, 0] := by
  funext j
  fin_cases j <;> decide

private theorem i0_values : data.iDz 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 0, 0] := by
  funext j
  fin_cases j <;> decide

private theorem i1_values : data.iDz 1 = ![0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1, 0, 1, 1] := by
  funext j
  fin_cases j <;> decide

/-- The equations extracted from the actual matrix, in normalized coordinates. -/
structure Equations (x : Fin 10 → ℤ) : Prop where
  h₁ : 1 + 9/(x 2 : ℚ) + 9/(x 3 : ℚ) + 1/(x 7 : ℚ) -
    16/(x 8 : ℚ) - 16/(x 9 : ℚ) = 0
  h₂ : 1 + x 2 + x 3 + x 7 - x 8 - x 9 = 0
  h₃ : x 2 + x 3 + x 4 = 0
  h₄ : 0 < 36/(x 2 : ℚ) + 36/(x 3 : ℚ) + 400/(x 4 : ℚ)

/-- Column differences give the displayed equations; positive orders give the strict bound. -/
theorem equations {x : Fin 10 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : Equations x := by
  have h0 : x 0 = 1 := hd.principal_degree
  have h1 : data.weightedColumn (degree x) (fun j => data.iDz 0 j - data.iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 1, sub_self]
  have h2 := hd.orthogonal_z 0
  have h2' := hd.orthogonal_z 1
  have h3 := hd.orthogonal_t
  have hp := ho.weighted_z_sub_t_pos 0
  simp only [weightedColumn, columnInner] at h1 h2 h2' h3 hp
  rw [z_values, i0_values, i1_values] at h1
  rw [i0_values] at h2
  rw [i1_values] at h2'
  rw [t_values] at h3
  rw [z_values, i0_values, t_values] at hp
  change (∑ j : Fin 15, _) = 0 at h1 h2 h2' h3
  change 0 < (∑ j : Fin 15, _) at hp
  norm_num [degree, label, Fin.sum_univ_succ, h0] at h1 h2 h2' h3 hp
  constructor
  · linear_combination h1
  · omega
  · omega
  · linear_combination hp

/-- The printed row with label two is separated only after separating the two degrees. -/
theorem row_separated_two {x : Fin 10 → ℤ} (hne : x 2 ≠ x 3) :
    data.RowSeparated (degree x) 5 := by
  apply separated_except (degree x) 5 7 (by decide) (by decide)
  exact Ne.symm hne

/-- The degree-13 prime bound uses the proved separation, not the printed label. -/
theorem prime_bound_two {x : Fin 10 → ℤ} {g : ℕ}
    (hp : data.PrimeConstraints (degree x) g) (hne : x 2 ≠ x 3)
    (hx : x 2 = -13) (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ 14 := by
  have hr : degree x 5 = -13 := hx
  have hb := hp.prime_bound 5 (by rw [hr]; decide)
    (row_separated_two hne) p hpp hpg
  simpa [hr] using hb

/-- The printed row with label three is separated only after separating the two degrees. -/
theorem row_separated_three {x : Fin 10 → ℤ} (hne : x 2 ≠ x 3) :
    data.RowSeparated (degree x) 7 := by
  apply separated_except (degree x) 7 5 (by decide) (by decide)
  exact hne

/-- The degree-13 prime bound uses the proved separation, not the printed label. -/
theorem prime_bound_three {x : Fin 10 → ℤ} {g : ℕ}
    (hp : data.PrimeConstraints (degree x) g) (hne : x 2 ≠ x 3)
    (hx : x 3 = -13) (p : ℕ) (hpp : p.Prime) (hpg : p ∣ g) : p ≤ 14 := by
  have hr : degree x 7 = -13 := hx
  have hb := hp.prime_bound 7 (by rw [hr]; decide)
    (row_separated_three hne) p hpp hpg
  simpa [hr] using hb


end EarlyL

end Stellmacher.Recognition.LyonsU3Four
