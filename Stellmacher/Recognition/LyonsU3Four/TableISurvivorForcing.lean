module

public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorDegrees
public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
public import Stellmacher.Recognition.LyonsU3Four.TableIGaloisNormalization
public import Stellmacher.Recognition.LyonsU3Four.TableIEarlyBounds
import Mathlib.Tactic

/-! The normalized U/V survivors of Table I.

The concrete matrices are used here to transport arbitrary signed degree
labels to the printed coordinates.  The small arithmetic records below are
the equations obtained by expanding the actual orthogonality and order
identities; they are kept separate from the common final calculation in
`TableISurvivorDegrees`. Signed multiplicity supplies each degree gap, and
the distinct rows supply the Schur prime bounds.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
Table I and the calculations (U), (V), pp. 385–386.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators

/-- Reciprocal bounds for a signed degree with a gap about zero. -/
theorem survivor_inv_bounds {x a b : ℤ} (ha : a < 0) (hb : 0 < b)
    (h : x ≤ a ∨ b ≤ x) : (a : ℚ)⁻¹ ≤ (x : ℚ)⁻¹ ∧ (x : ℚ)⁻¹ ≤ (b : ℚ)⁻¹ := by
  have ha' : (a : ℚ) < 0 := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rcases h with h | h
  · have hx : (x : ℚ) ≤ a := by exact_mod_cast h
    have hn := hx.trans_lt ha'
    exact ⟨(inv_le_inv_of_neg ha' hn).mpr hx,
      (le_of_lt (inv_neg''.mpr hn)).trans (le_of_lt (inv_pos.mpr hb'))⟩
  · have hx : (b : ℚ) ≤ x := by exact_mod_cast h
    have hp := hb'.trans_le hx
    exact ⟨(le_of_lt (inv_neg''.mpr ha')).trans (le_of_lt (inv_pos.mpr hp)),
      (inv_le_inv₀ hp hb').mpr hx⟩

namespace SurvivorU

abbrev data : GeneralizedDecompositionData (Fin 18) := tableIData .U ()

def label : Fin 18 → Fin 8 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 6, 7]
def representative : Fin 8 → Fin 18 := ![0, 1, 5, 9, 13, 15, 16, 17]
def degree (x : Fin 8 → ℤ) : Fin 18 → ℤ := fun j => x (label j)

def galoisLabeling : data.GaloisLabeling 0 (Fin 8) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

theorem normalize_degree {r : Fin 18 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r) (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 8 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧ data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

theorem degree_representative (x : Fin 8 → ℤ) (i : Fin 8) :
    degree x (representative i) = x i := by fin_cases i <;> rfl

def offset : Fin 8 → ℤ := ![63, -51, 12, 63, -39, 150, 63, 12]

theorem degree_mod {x : Fin 8 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 8) : (x i + offset i) % 64 = 0 := by
  have hm := h.multiplicity_integral (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  simpa only [degree_representative, add_assoc, hb, Int.ModEq, Int.zero_emod] using hm

def lower : Fin 8 → ℤ := ![-63, -13, -12, -63, -25, -150, -63, -12]
def upper : Fin 8 → ℤ := ![65, 51, 52, 65, 39, 42, 65, 52]

theorem degree_nonzero {x : Fin 8 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 8) : x i ≠ 0 := by
  simpa only [degree_representative] using h.degree_nonzero (representative i)

/-- Signed multiplicity and the residue modulo 64 bound each nonprincipal degree. -/
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

/-- The rows used for Schur's bound are distinct even up to sign. -/
theorem row_separated (x : Fin 8 → ℤ) (i : Fin 8) (hi : i = 1 ∨ i = 2 ∨ i = 4) :
    data.RowSeparated (degree x) (representative i) := by
  intro k ε hε hr ht hz
  clear hr
  rcases hi with rfl | rfl | rfl
  all_goals rcases sq_eq_one_iff.mp hε with rfl | rfl
  all_goals revert k; decide

/-- A prime divisor of any degree is bounded using a separated degree. -/
theorem prime_bound {x : Fin 8 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x)) (hp : data.PrimeConstraints (degree x) g)
    (i : Fin 8) (hi : i = 1 ∨ i = 2 ∨ i = 4) (k : Fin 8)
    (p : ℕ) (hpp : p.Prime) (hpk : p ∣ (x k).natAbs) : p ≤ (x i).natAbs + 1 := by
  have hn : representative i ≠ 0 := by rcases hi with rfl | rfl | rfl <;> decide
  have hl := hd.degree_lower (representative i) hn
  have hh := hp.prime_dvd_degree_le (by omega) (row_separated x i hi)
    (representative k) hpp (by simpa only [degree_representative] using hpk)
  simpa only [degree_representative] using hh

theorem z_values : data.zValue =
    ![1, 3, 3, 3, 3, 4, 4, 4, 4, 1, 1, 1, 1, 7, 7, 10, 1, 4] := by
  funext j; fin_cases j <;> decide
theorem t_values : data.dT =
    ![1, -1, -1, -1, -1, 0, 0, 0, 0, 1, 1, 1, 1, -1, -1, 2, 1, 0] := by
  funext j; fin_cases j <;> decide
theorem i0_values : data.iDz 0 =
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 2, 1, 0] := by
  funext j; fin_cases j <;> decide
theorem i1_values : data.iDz 1 =
    ![0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 2, 1, 2, 0, 1] := by
  funext j; fin_cases j <;> decide
private theorem i2_values : data.iDz 2 =
    ![0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 2, 2, 0, 1] := by
  funext j; fin_cases j <;> decide

structure Equations (x : Fin 8 → ℤ) : Prop where
  h₁ : 1 - 36/(x 1 : ℚ) + 4/(x 3 : ℚ) - 98/(x 4 : ℚ) +
      200/(x 5 : ℚ) + 1/(x 6 : ℚ) = 0
  h₂ : 1 + 18/(x 1 : ℚ) + 16/(x 2 : ℚ) - 1/(x 3 : ℚ) -
      49/(x 4 : ℚ) + 1/(x 6 : ℚ) - 16/(x 7 : ℚ) = 0
  h₃ : 0 < 1 + 36/(x 1 : ℚ) + 64/(x 2 : ℚ) + 98/(x 4 : ℚ) +
      200/(x 5 : ℚ) + 1/(x 6 : ℚ)

theorem equations {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : Equations x := by
  have h1 := ho.zero_t
  have h2 : data.weightedColumn (degree x)
      (fun j => data.iDz 0 j - data.iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 0, ho.equal_z 1]
    exact sub_self _
  have h3 := ho.weighted_z_pos 0
  simp only [weightedColumn] at h1 h2 h3
  rw [z_values, t_values] at h1
  rw [z_values, i0_values, i1_values] at h2
  rw [z_values, i0_values] at h3
  norm_num [degree, label, Fin.sum_univ_succ] at h1 h2 h3
  have hx0 : x 0 = 1 := hd.principal_degree
  rw [hx0] at h1 h2 h3
  ring_nf at h1 h2 h3
  constructor
  · convert h1 using 1
    ring
  · convert h2 using 1
    ring
  · convert h3 using 1
    ring

def coordinate (h : UPrefix) : Fin 8 → ℤ :=
  ![1, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7]

def degree_twelve_witness (h : UPrefix) :
    DegreeTwelveWitness data (degree (coordinate h)) := by
  have hf := survivorU_forced h
  refine {
    row := representative 7
    abs_degree := ?_
    unique := ?_
    weight_identity := ?_ }
  · change (coordinate h 7).natAbs = 12
    simp [coordinate, hf]
  · intro j hj
    fin_cases j <;> simp [degree, coordinate, label, representative, hf] at hj ⊢
  · simp only [weightedColumn]
    rw [z_values, i0_values]
    simp [degree, coordinate, label, hf, Fin.sum_univ_succ]
    norm_num

end SurvivorU

namespace SurvivorV

abbrev data : GeneralizedDecompositionData (Fin 21) := tableIData .V ()
def label : Fin 21 → Fin 11 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10]
def representative : Fin 11 → Fin 21 := ![0, 1, 5, 9, 13, 15, 16, 17, 18, 19, 20]
def degree (x : Fin 11 → ℤ) : Fin 21 → ℤ := fun j => x (label j)
def middleIndex (i : Fin 4) : Fin 11 := ⟨i.val + 5, by omega⟩

def galoisLabeling : data.GaloisLabeling 0 (Fin 11) where
  label := label
  representative := representative
  step := ![0, 0, 1, 2, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0]
  row_eq := by decide
  step_eq := by decide
  coordinates_injective := by decide
  principal_step := rfl
  principal_representative := rfl

theorem normalize_degree {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r) (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) :
    ∃ x : Fin 11 → ℤ, data.DegreeConstraints 0 (degree x) ∧
      data.OrderConstraints (degree x) g c e ∧ data.PrimeConstraints (degree x) g := by
  exact galoisLabeling.normalize (by decide) hd ho hp

theorem degree_representative (x : Fin 11 → ℤ) (i : Fin 11) :
    degree x (representative i) = x i := by fin_cases i <;> rfl

def offset : Fin 11 → ℤ := ![63, -51, 12, 63, -39, 75, 75, 75, 75, 63, 12]

theorem degree_mod {x : Fin 11 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 11) : (x i + offset i) % 64 = 0 := by
  have hm := h.multiplicity_integral (representative i)
  have hb : 3 * data.zValue (representative i) + 60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  simpa only [degree_representative, add_assoc, hb, Int.ModEq, Int.zero_emod] using hm

def lower : Fin 11 → ℤ := ![-63, -13, -12, -63, -25, -75, -75, -75, -75, -63, -12]
def upper : Fin 11 → ℤ := ![65, 51, 52, 65, 39, 53, 53, 53, 53, 65, 52]

theorem degree_nonzero {x : Fin 11 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 11) : x i ≠ 0 := by
  simpa only [degree_representative] using h.degree_nonzero (representative i)

/-- Signed multiplicity and the residue modulo 64 bound each nonprincipal degree. -/
theorem degree_bounds {x : Fin 11 → ℤ} (h : data.DegreeConstraints 0 (degree x))
    (i : Fin 11) (hi : i ≠ 0) : x i ≤ lower i ∨ upper i ≤ x i := by
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

/-- The rows used for Schur's bound are distinct even up to sign. -/
theorem row_separated (x : Fin 11 → ℤ) (i : Fin 11) (hi : i = 1 ∨ i = 2 ∨ i = 4) :
    data.RowSeparated (degree x) (representative i) := by
  intro k ε hε hr ht hz
  clear hr
  rcases hi with rfl | rfl | rfl
  all_goals rcases sq_eq_one_iff.mp hε with rfl | rfl
  all_goals revert k; decide

/-- A prime divisor of any degree is bounded using a separated degree. -/
theorem prime_bound {x : Fin 11 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x)) (hp : data.PrimeConstraints (degree x) g)
    (i : Fin 11) (hi : i = 1 ∨ i = 2 ∨ i = 4) (k : Fin 11)
    (p : ℕ) (hpp : p.Prime) (hpk : p ∣ (x k).natAbs) : p ≤ (x i).natAbs + 1 := by
  have hn : representative i ≠ 0 := by rcases hi with rfl | rfl | rfl <;> decide
  have hl := hd.degree_lower (representative i) hn
  have hh := hp.prime_dvd_degree_le (by omega) (row_separated x i hi)
    (representative k) hpp (by simpa only [degree_representative] using hpk)
  simpa only [degree_representative] using hh

theorem z_values : data.zValue =
    ![1, 3, 3, 3, 3, 4, 4, 4, 4, 1, 1, 1, 1, 7, 7, 5, 5, 5, 5, 1, 4] := by
  funext j; fin_cases j <;> decide
theorem t_values : data.dT =
    ![1, -1, -1, -1, -1, 0, 0, 0, 0, 1, 1, 1, 1, -1, -1,
      1, 1, 1, 1, 1, 0] := by
  funext j; fin_cases j <;> decide
theorem i0_values : data.iDz 0 =
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1,
      1, 1, 1, 1, 1, 0] := by
  funext j; fin_cases j <;> decide
theorem i1_values : data.iDz 1 =
    ![0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 2, 1,
      1, 1, 1, 1, 0, 1] := by
  funext j; fin_cases j <;> decide

structure Equations (x : Fin 11 → ℤ) : Prop where
  h₁ : 1 - 36/(x 1 : ℚ) + 4/(x 3 : ℚ) - 98/(x 4 : ℚ) +
      (∑ i : Fin 4, 25/(x (middleIndex i) : ℚ)) +
      1/(x 9 : ℚ) = 0
  h₂ : 1 + 18/(x 1 : ℚ) + 16/(x 2 : ℚ) - 1/(x 3 : ℚ) -
      49/(x 4 : ℚ) + 1/(x 9 : ℚ) - 16/(x 10 : ℚ) = 0
  h₃ : 0 < 1 + 36/(x 1 : ℚ) + 64/(x 2 : ℚ) + 98/(x 4 : ℚ) +
      (∑ i : Fin 4, 25/(x (middleIndex i) : ℚ)) +
      1/(x 9 : ℚ)

theorem equations {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : Equations x := by
  have h1 := ho.zero_t
  have h2 : data.weightedColumn (degree x)
      (fun j => data.iDz 0 j - data.iDz 1 j) = 0 := by
    rw [weightedColumn_sub, ho.equal_z 0, ho.equal_z 1]
    exact sub_self _
  have h3 := ho.weighted_z_pos 0
  simp only [weightedColumn] at h1 h2 h3
  rw [z_values, t_values] at h1
  rw [z_values, i0_values, i1_values] at h2
  rw [z_values, i0_values] at h3
  norm_num [degree, label, Fin.sum_univ_succ] at h1 h2 h3
  have hx0 : x 0 = 1 := hd.principal_degree
  rw [hx0] at h1 h2 h3
  ring_nf at h1 h2 h3
  constructor
  · convert h1 using 1
    simp [middleIndex, Fin.sum_univ_succ]
    ring
  · convert h2 using 1
    ring
  · convert h3 using 1
    simp [middleIndex, Fin.sum_univ_succ]
    ring

def coordinate (h : VPrefix) : Fin 11 → ℤ :=
  ![1, h.x1, h.x2, h.x3, h.x4, h.middle 0, h.middle 1, h.middle 2,
    h.middle 3, h.x6, h.x7]

def degree_twelve_witness (h : VPrefix) :
    DegreeTwelveWitness data (degree (coordinate h)) := by
  have hf := survivorV_forced h
  refine {
    row := representative 10
    abs_degree := ?_
    unique := ?_
    weight_identity := ?_ }
  · change (coordinate h 10).natAbs = 12
    simp [coordinate, hf]
  · intro j hj
    fin_cases j <;> simp [degree, coordinate, label, representative, hf] at hj ⊢
  · simp only [weightedColumn]
    rw [z_values, i0_values]
    simp [degree, coordinate, label, hf, Fin.sum_univ_succ]
    norm_num

end SurvivorV

end Stellmacher.Recognition.LyonsU3Four
