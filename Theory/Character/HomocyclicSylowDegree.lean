module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

/-!
# The degree-one step in Brauer's homocyclic Sylow theorem

Brauer's character calculation produces three positive degrees and three signs.
The first two signed degrees are minus one modulo the Sylow order, and
ordinary and reciprocal degree relations connect all three. When the Sylow
order is divisible by sixteen, one of the first two degrees must be one.

If both exceed one, their congruences bound them below by fifteen. The
reciprocal relation then forces the third sign to be positive and the third
degree to be at most ten. The ordinary relation fixes that degree to three
modulo sixteen, hence to three. This contradicts the reciprocal relation.

Source: R. Brauer, *Some applications of the theory of blocks of characters
of finite groups. II*, J. Algebra 1 (1964), 307–334, §VI, p.319, equations
(6.7)–(6.9). This is only the numerical deduction; the character construction
and its identities are separate mathematical inputs.
-/

/-- The signed degree identities force a linear character. Divisibility by
sixteen suffices, so the statement also applies when the original congruences
are modulo `2 ^ (2 * n)` with `n ≥ 2`. -/
public theorem degree_eq_one_of_homocyclic_relations (a b c d e f : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hma : 16 ∣ a + d) (hmb : 16 ∣ b + e)
    (hdeg : -1 + d * a + e * b + f * c = 0)
    (hrec : -(1 : ℚ) + d / (a : ℚ) + e / (b : ℚ) + 9 * f / (c : ℚ) = 0) :
    a = 1 ∨ b = 1 := by
  by_contra h
  push Not at h
  have hma' := Int.emod_eq_zero_of_dvd hma
  have hmb' := Int.emod_eq_zero_of_dvd hmb
  have ha15 : 15 ≤ a := by rcases hd with rfl | rfl <;> omega
  have hb15 : 15 ≤ b := by rcases he with rfl | rfl <;> omega
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
  have hda : (d : ℚ) / a ≤ 1 / 15 := by
    apply (div_le_iff₀ haQ).mpr
    have hd1 : d ≤ 1 := by omega
    have hd1Q : (d : ℚ) ≤ 1 := by exact_mod_cast hd1
    have ha15Q : (15 : ℚ) ≤ a := by exact_mod_cast ha15
    linarith
  have heb : (e : ℚ) / b ≤ 1 / 15 := by
    apply (div_le_iff₀ hbQ).mpr
    have he1 : e ≤ 1 := by omega
    have he1Q : (e : ℚ) ≤ 1 := by exact_mod_cast he1
    have hb15Q : (15 : ℚ) ≤ b := by exact_mod_cast hb15
    linarith
  have hfc : (13 : ℚ) / 15 ≤ 9 * f / c := by linarith
  have hfc' := (le_div_iff₀ hcQ).mp hfc
  have hf1 : f = 1 := by
    rcases hf with h | h
    · exact h
    · rw [h] at hfc'
      norm_num at hfc'
      linarith
  have hc10 : c ≤ 10 := by
    rw [hf1] at hfc'
    have : (c : ℚ) < 11 := by norm_num at hfc'; linarith
    have : c < 11 := by exact_mod_cast this
    omega
  have hc3 : c = 3 := by
    rw [hf1] at hdeg
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;>
      simp only [one_mul, neg_one_mul] at hdeg <;> omega
  have hda' : -(1 : ℚ) / 15 ≤ (d : ℚ) / a := by
    apply (le_div_iff₀ haQ).mpr
    have hd1 : -1 ≤ d := by omega
    have hd1Q : -(1 : ℚ) ≤ d := by exact_mod_cast hd1
    have ha15Q : (15 : ℚ) ≤ a := by exact_mod_cast ha15
    linarith
  have heb' : -(1 : ℚ) / 15 ≤ (e : ℚ) / b := by
    apply (le_div_iff₀ hbQ).mpr
    have he1 : -1 ≤ e := by omega
    have he1Q : -(1 : ℚ) ≤ e := by exact_mod_cast he1
    have hb15Q : (15 : ℚ) ≤ b := by exact_mod_cast hb15
    linarith
  rw [hf1, hc3] at hrec
  norm_num at hrec
  linarith
