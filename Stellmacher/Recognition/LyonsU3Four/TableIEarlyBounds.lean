module

public import Stellmacher.Recognition.LyonsU3Four.TableIOrderPositivity

/-!
# Signed-degree bounds for the early Table I cases

The row sign changes affect both the degree and the restriction multiplicity.
We combine their product's nonnegativity with divisibility by 64 and the
nonprincipal degree bound. These are the bounds used in Lyons's eliminations
on pp. 382–384. Positivity of the weighted column follows from Lemma 4(c),
with the positive orders still explicit.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Lemmas 4–5; local PDF:
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {principal : I} {degree : I → ℤ}

/-- The signed numerator and degree have the same weak sign. -/
theorem DegreeConstraints.multiplicity_sign
    (h : d.DegreeConstraints principal degree) (j : I) :
    (0 < degree j → 0 ≤ degree j + 3*d.zValue j + 60*d.dT j) ∧
    (degree j < 0 → degree j + 3*d.zValue j + 60*d.dT j ≤ 0) := by
  have hh := h.multiplicity_nonneg j
  constructor <;> intro hj <;> nlinarith

/-- Bounds for a row with `dᵗ = 1` and `χ(z) = 1`. -/
theorem DegreeConstraints.bounds_t1_z1
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = 1) (hz : d.zValue j = 1) :
    degree j ≤ -63 ∨ 65 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + 63) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + 63 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + 63 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = -1` and `χ(z) = 3`. -/
theorem DegreeConstraints.bounds_tneg1_z3
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = -1) (hz : d.zValue j = 3) :
    degree j ≤ -13 ∨ 51 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + -51) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + -51 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + -51 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = 1` and `χ(z) = 5`. -/
theorem DegreeConstraints.bounds_t1_z5
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = 1) (hz : d.zValue j = 5) :
    degree j ≤ -75 ∨ 53 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + 75) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + 75 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + 75 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = -2` and `χ(z) = 10`. -/
theorem DegreeConstraints.bounds_tneg2_z10
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = -2) (hz : d.zValue j = 10) :
    degree j ≤ -38 ∨ 90 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + -90) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + -90 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + -90 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = 1` and `χ(z) = 9`. -/
theorem DegreeConstraints.bounds_t1_z9
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = 1) (hz : d.zValue j = 9) :
    degree j ≤ -87 ∨ 41 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + 87) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + 87 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + 87 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = 0` and `χ(z) = 4`. -/
theorem DegreeConstraints.bounds_t0_z4
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = 0) (hz : d.zValue j = 4) :
    degree j ≤ -12 ∨ 52 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + 12) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + 12 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + 12 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = -3` and `χ(z) = 5`. -/
theorem DegreeConstraints.bounds_tneg3_z5
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = -3) (hz : d.zValue j = 5) :
    degree j ≤ -27 ∨ 165 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + -165) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + -165 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + -165 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = 2` and `χ(z) = 6`. -/
theorem DegreeConstraints.bounds_t2_z6
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = 2) (hz : d.zValue j = 6) :
    degree j ≤ -138 ∨ 54 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + 138) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + 138 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + 138 := by nlinarith
    omega

/-- Bounds for a row with `dᵗ = -1` and `χ(z) = 7`. -/
theorem DegreeConstraints.bounds_tneg1_z7
    (h : d.DegreeConstraints principal degree) (j : I) (hj : j ≠ principal)
    (ht : d.dT j = -1) (hz : d.zValue j = 7) :
    degree j ≤ -25 ∨ 39 ≤ degree j := by
  have hm := h.multiplicity_integral j
  have hn := h.multiplicity_nonneg j
  have ha := h.degree_lower j hj
  rw [ht, hz] at hm hn
  have hmod : (degree j + -39) % 64 = 0 := by
    simpa [Int.ModEq, add_assoc] using hm
  by_cases hs : degree j < 0
  · left
    have : degree j + -39 ≤ 0 := by nlinarith [h.degree_nonzero j]
    omega
  · right
    have : (12 : ℤ) ≤ degree j := by omega
    have : 0 ≤ degree j + -39 := by nlinarith
    omega

/-- The positive difference used in cases B, C and L. -/
theorem OrderConstraints.weighted_z_sub_t_pos {g c e : ℕ}
    (h : d.OrderConstraints degree g c e) (i : Fin 5) :
    0 < d.weightedColumn degree (fun j => d.iDz i j - d.dT j) := by
  rw [weightedColumn_sub, h.zero_t, sub_zero]
  exact h.weighted_z_pos i

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
