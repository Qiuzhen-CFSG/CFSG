module

public import Stellmacher.Recognition.LyonsU3Four.TableIPatterns
public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData
public import Stellmacher.Recognition.LyonsU3Four.TableILateNumerical
public import Stellmacher.Recognition.LyonsU3Four.TableILateEquationData
public import Stellmacher.Recognition.LyonsU3Four.TableILateNT
public import Stellmacher.Recognition.LyonsU3Four.TableILateNormalization
public import Stellmacher.Recognition.LyonsU3Four.TableIMatrices
import Mathlib.Tactic

/-!
# The late eliminations in Table I

The seven matrices M, N, P, Q, R, S and T admit no signed integer degrees
satisfying the degree, order and prime constraints. Galois normalization
aligns arbitrary degrees with the printed labels, after which the numerical
contradictions apply. The degree constraints retain both integrality and
nonnegativity of the signed restriction multiplicities. Row separation is
proved before invoking the prime bounds.

`LateM.impossible_degrees` through `LateT.impossible_degrees` are the explicit
matrix endpoints. The matrices are identified with the canonical catalogue;
`tableI_late_impossible` excludes all seven catalogue cases, and
`tableI_late_impossible_of_signed_matrix` transports this exclusion through
an explicit signed row equivalence. The abstract case tags in `TableIPatterns`
alone do not supply that equivalence. Exhaustive classification remains the
responsibility of the consumer. The older terminal certificates are retained
for compatibility.

The weighted-column equations and positivity inequalities are derived in
`TableILateMatrices` and `TableILateEquationData`. The arithmetic is in
`TableILateNumerical` and `TableILateNT`. These proofs resolve the source's
closing T sign as `x₆ < 0`, after its positive case has been contradicted.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, pp. 384--385,
cases (M)--(T).
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four

open GeneralizedDecompositionData

namespace LateM

/-- Case M is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox hpx

/-- The numerical model is exactly the canonical case M matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .M () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateM

namespace LateN

/-- Case N is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox hpx

/-- The numerical model is exactly the canonical case N matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .N () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateN

namespace LateP

/-- Case P is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 23 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox

/-- The numerical model is exactly the canonical case P matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .P () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateP

namespace LateQ

/-- Case Q is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 21 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox

/-- The numerical model is exactly the canonical case Q matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .Q () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateQ

namespace LateR

/-- Case R is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 23 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox

/-- The numerical model is exactly the canonical case R matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .R () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateR

namespace LateS

/-- Case S is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 19 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox

/-- The numerical model is exactly the canonical case S matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .S () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateS

namespace LateT

/-- Case T is impossible for arbitrary signed degrees on its full row set. -/
theorem impossible_degrees {r : Fin 17 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 r)
    (ho : data.OrderConstraints r g c e)
    (hp : data.PrimeConstraints r g) : False := by
  obtain ⟨x, hdx, hox, hpx⟩ := normalize_degree hd ho hp
  exact impossible hdx hox hpx

/-- The numerical model is exactly the canonical case T matrix. -/
theorem matrix_eq_catalogue : matrix = tableIMatrix .T () := by
  funext j k
  fin_cases j <;> fin_cases k <;> rfl

end LateT

/-- All seven late catalogue matrices are excluded by the numerical constraints. -/
theorem tableI_late_impossible (a : TableICase) (v : a.Variant)
    (ha : a ∈ [TableICase.M, .N, .P, .Q, .R, .S, .T])
    {r : Fin (tableIRowCount a) → ℤ} {g c e : ℕ}
    (hd : (tableIData a v).DegreeConstraints (tableIPrincipal a) r)
    (ho : (tableIData a v).OrderConstraints r g c e)
    (hp : (tableIData a v).PrimeConstraints r g) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases v
    have heq : tableIData .M () = LateM.data := by
      unfold tableIData LateM.data
      rw [← LateM.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateM.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .N () = LateN.data := by
      unfold tableIData LateN.data
      rw [← LateN.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateN.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .P () = LateP.data := by
      unfold tableIData LateP.data
      rw [← LateP.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateP.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .Q () = LateQ.data := by
      unfold tableIData LateQ.data
      rw [← LateQ.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateQ.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .R () = LateR.data := by
      unfold tableIData LateR.data
      rw [← LateR.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateR.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .S () = LateS.data := by
      unfold tableIData LateS.data
      rw [← LateS.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateS.impossible_degrees hd ho hp
  · cases v
    have heq : tableIData .T () = LateT.data := by
      unfold tableIData LateT.data
      rw [← LateT.matrix_eq_catalogue]
      rfl
    rw [heq] at hd ho hp
    exact LateT.impossible_degrees hd ho hp

/-- Exclude a late case identified by a signed row equivalence. The principal
sign follows from the pattern hypotheses, and all numerical constraints,
including row separation, are transported by the same signs. -/
theorem tableI_late_impossible_of_signed_matrix
    {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {principal : I} {r : I → ℤ} {g c z : ℕ}
    (a : TableICase) (v : a.Variant)
    (ha : a ∈ [TableICase.M, .N, .P, .Q, .R, .S, .T])
    (e : I ≃ Fin (tableIRowCount a)) (ε : I → ℤ)
    (hε : ∀ j, ε j ^ 2 = 1)
    (hm : ∀ j k, d.tableIRow j k = ε j * tableIMatrix a v (e j) k)
    (he : e principal = tableIPrincipal a)
    (hpat : d.TableIPatternHypotheses principal)
    (hd : d.DegreeConstraints principal r)
    (ho : d.OrderConstraints r g c z)
    (hp : d.PrimeConstraints r g) : False := by
  have hq : tableIMatrix a v (tableIPrincipal a) 0 = 1 := by
    rw [tableIMatrix_principal]
    rfl
  obtain ⟨hd', ho', hp'⟩ := constraints_of_signed_matrix e ε hε hm he
    hpat.principal_dT hq hd ho hp
  exact tableI_late_impossible a v ha hd' ho' hp'

/-! A convenient bridge for row calculations.  In applications `hrow` is
obtained by unfolding `tableIRow` after the signed row permutation. -/

theorem weightedColumn_eq_sum {I : Type*} [Fintype I]
    (d : GeneralizedDecompositionData I) (degree a : I → ℤ)
    (hrow : ∀ j, d.dT j = a j) :
    d.weightedColumn degree d.dT =
      ∑ j, (d.zValue j : LateRational) ^ 2 * lateCast (a j) / lateCast (degree j) := by
  simp only [weightedColumn, hrow]
  rfl

theorem weightedColumn_iDz_eq_sum {I : Type*} [Fintype I]
    (d : GeneralizedDecompositionData I) (degree : I → ℤ) (i : Fin 5)
    (a : I → ℤ) (hrow : ∀ j, d.iDz i j = a j) :
    d.weightedColumn degree (d.iDz i) =
      ∑ j, (d.zValue j : LateRational) ^ 2 * lateCast (a j) / lateCast (degree j) := by
  simp only [weightedColumn, hrow]
  rfl

/-! Terminal arithmetic certificates.  The hypotheses are exactly the
inequalities left after the row-separation and prime-bound steps in the
paper. -/

theorem eliminate_M_terminal (y : ℤ) (hmod : Int.ModEq 64 y 52)
    (hlo : -140 < y) (hhi : y < -12) (hne : y ≠ -76) : False := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod)
  change 52 - y = 64 * k at hk
  interval_cases y <;> norm_num at hmod
  all_goals omega

theorem eliminate_N_terminal₁ (x₇ : ℤ) (_hmod : Int.ModEq 64 x₇ 41)
    (hb : x₇.natAbs ≤ 63) (hval : x₇ = 141) : False := by
  omega

theorem eliminate_N_terminal₂ (x₃ : ℤ) (hmod : Int.ModEq 64 x₃ 52)
    (hlo : 0 < x₃) (hhi : x₃ < 40) : False := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod)
  change 52 - x₃ = 64 * k at hk
  interval_cases x₃ <;> norm_num at hmod

theorem eliminate_P_terminal (x₁ x₂ x₆ : ℤ)
    (h : 1 / lateCast x₁ + 1 / lateCast x₂ - 1 / lateCast x₆ = -(9 : LateRational) / 247)
    (hx₁ : x₁ = -63) (hx₂ : x₂ = -63)
    (hnz : x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₆ ≠ 0) : False := by
  rw [hx₁, hx₂] at h
  norm_num [lateCast] at h
  have hq : (73 : LateRational) * lateCast x₆ = 15561 := by
    change (73 : LateRational) * (x₆ : LateRational) = 15561
    field_simp [hnz.2.2] at h
    ring_nf at h
    nlinarith [h]
  have hi : (73 : ℤ) * x₆ = 15561 := by
    change (73 : LateRational) * (x₆ : LateRational) = 15561 at hq
    exact_mod_cast hq
  omega

theorem eliminate_Q_terminal (x₅ : ℤ) (hmod : Int.ModEq 64 x₅ 37)
    (hlo : 37 < x₅) (hhi : x₅ < 101) : False := by
  interval_cases x₅ <;> norm_num at hmod

theorem eliminate_R_terminal (x₇ : ℤ) (hmod : Int.ModEq 256 x₇ 53)
    (hlo : -165 < x₇) (hhi : x₇ < 0) : False := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod)
  change 53 - x₇ = 256 * k at hk
  interval_cases x₇ <;> norm_num at hmod

theorem eliminate_S_terminal :
    ¬ (0 > (8 : LateRational) - 144 / 51 - 96 / 114 - 100 / 75 -
      100 / 75 - 64 / 52) := by
  norm_num

theorem eliminate_T_terminal (x₁ : ℤ)
    (hmod : Int.ModEq 64 x₁ 51) (hlo : -108 < x₁) (hhi : x₁ < 0)
    (hne₁ : x₁ ≠ -77) (hne₂ : x₁ ≠ -13) : False := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hmod)
  change 51 - x₁ = 64 * k at hk
  interval_cases x₁ <;> norm_num at hmod
  all_goals first | exact hne₁ rfl | exact hne₂ rfl

/-! The common signed bound used by the preceding certificates. -/

theorem degree_modEq_of_multiplicity_integral
    {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {principal : I} {degree : I → ℤ}
    (h : d.DegreeConstraints principal degree) (j : I) (r : ℤ)
    (hr : 3 * d.zValue j + 60 * d.dT j = r) :
    Int.ModEq 64 (degree j + r) 0 := by
  rw [← hr]
  simpa [add_assoc] using h.multiplicity_integral j

theorem prime_bound_for_row
    {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {degree : I → ℤ} {g : ℕ} (h : d.PrimeConstraints degree g)
    {j : I} (hj : 5 < (degree j).natAbs) (hsep : d.RowSeparated degree j)
    {p : ℕ} (hp : p.Prime) (hpk : p ∣ (degree j).natAbs) :
    p ≤ (degree j).natAbs + 1 := by
  exact h.prime_bound j hj hsep p hp (hpk.trans (h.degree_dvd j))

end Stellmacher.Recognition.LyonsU3Four
