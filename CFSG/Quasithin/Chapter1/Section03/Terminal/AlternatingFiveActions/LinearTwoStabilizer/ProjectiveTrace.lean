module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Projective trace separation for the terminal A₅ argument

Squared matrix trace is well defined on the actual quotient SL₂/Z(SL₂).
For an element of projective order five, Cayley–Hamilton gives
`t⁴ - 3t² + 1 = 0`. This prevents its squared trace from agreeing with
that of its square in characteristic different from five. Inner and diagonal
actions preserve squared trace, and a prime field has no nontrivial field
automorphisms, so the proved semilinear coverage theorem gives invariance
under every ambient automorphism.

This supplies the matrix step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, proof of Lemma 1.3.9, printed p.514, for A.3.12(8), p.47.
The quotient and diagonal actions are the existing concrete PSL₂ model.
-/

public section

open Matrix
namespace CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer
open Theory.PSL2 Theory.PSL2.OuterSolvable Theory.PSL2.OuterSolvable.OddCoverage
variable {F : Type*} [Field F]

private theorem trace_sq_eq_of_quotient_eq (A B : SpecialLinearGroup (Fin 2) F)
    (h : quotientMap F A = quotientMap F B) : trace A.val ^ 2 = trace B.val ^ 2 := by
  rcases (quotientMap_eq_iff A B).mp h with rfl | rfl
  · rfl
  · simp

noncomputable def projectiveTraceSquared (x : Theory.PSL2.Group F) : F :=
  trace (quotientMap_surjective F x).choose.val ^ 2

theorem projectiveTraceSquared_mk (A : SpecialLinearGroup (Fin 2) F) :
    projectiveTraceSquared (quotientMap F A) = trace A.val ^ 2 :=
  trace_sq_eq_of_quotient_eq _ A (quotientMap_surjective F (quotientMap F A)).choose_spec

theorem projectiveTraceSquared_conj (g x : Theory.PSL2.Group F) :
    projectiveTraceSquared (g * x * g⁻¹) = projectiveTraceSquared x := by
  obtain ⟨A, rfl⟩ := quotientMap_surjective F g
  obtain ⟨B, rfl⟩ := quotientMap_surjective F x
  rw [← map_inv, ← map_mul, ← map_mul, projectiveTraceSquared_mk, projectiveTraceSquared_mk]
  congr 1
  let c : SpecialLinearGroup (Fin 2) F →* Matrix (Fin 2) (Fin 2) F :=
    SpecialLinearGroup.coeMonoidHom
  change trace (c (A * B * A⁻¹)) = trace (c B)
  rw [map_mul, map_mul, trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem projectiveTraceSquared_diagonal (u : Fˣ) (x : Theory.PSL2.Group F) :
    projectiveTraceSquared (diagonalAutHom u x) = projectiveTraceSquared x := by
  obtain ⟨A, rfl⟩ := quotientMap_surjective F x
  rw [diagonalAutHom_apply_quotientMap, projectiveTraceSquared_mk, projectiveTraceSquared_mk]
  rfl

private theorem sl_pow_two (A : SpecialLinearGroup (Fin 2) F) :
    A.val ^ 2 = trace A.val • A.val - 1 := by
  have hd := A.property
  simp only [det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, mul_apply, Fin.sum_univ_two, trace] <;>
      first | (solve | ring) | linear_combination -hd

private theorem sl_pow_five (A : SpecialLinearGroup (Fin 2) F) :
    A.val ^ 5 = (trace A.val ^ 4 - 3 * trace A.val ^ 2 + 1) • A.val +
      (-trace A.val ^ 3 + 2 * trace A.val) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h2 := sl_pow_two A
  calc
    A.val ^ 5 = A.val ^ 2 * A.val ^ 2 * A.val := by noncomm_ring
    _ = _ := by
      rw [h2]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      simp only [← pow_two A.val, h2, smul_sub, smul_smul, sub_mul,
        smul_mul_assoc, one_mul]
      module

private theorem trace_sq_polynomial_of_order_five (A : SpecialLinearGroup (Fin 2) F)
    (horder : orderOf (quotientMap F A) = 5) :
    trace A.val ^ 4 - 3 * trace A.val ^ 2 + 1 = 0 := by
  have hpow : quotientMap F (A ^ 5) = quotientMap F 1 := by
    rw [map_pow, map_one, ← horder, pow_orderOf_eq_one]
  have hscalar : ∃ z : F, A.val ^ 5 = z • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rcases (quotientMap_eq_iff _ _).mp hpow with h | h
    · refine ⟨1, ?_⟩
      simpa using congrArg (fun X : SpecialLinearGroup (Fin 2) F => X.val) h
    · refine ⟨-1, ?_⟩
      simpa using congrArg (fun X : SpecialLinearGroup (Fin 2) F => X.val) h
  obtain ⟨z, hz⟩ := hscalar
  rw [sl_pow_five] at hz
  by_contra hn
  have hA : A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    apply SpecialLinearGroup.mem_center_iff.mpr
    let c := trace A.val ^ 4 - 3 * trace A.val ^ 2 + 1
    let d := -trace A.val ^ 3 + 2 * trace A.val
    have he : A.val = ((z - d) / c) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have hh : c • A.val = (z - d) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [sub_smul]
        exact eq_sub_of_add_eq hz
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => c⁻¹ • M) hh
      simpa [smul_smul, c, hn, div_eq_mul_inv, mul_comm] using this
    refine ⟨(z - d) / c, ?_, ?_⟩
    · have hd := A.property
      rw [he] at hd
      simpa using hd
    · change Matrix.diagonal (fun _ => (z - d) / c) = A.val
      simpa only [Matrix.smul_one_eq_diagonal] using he.symm
  have hone : quotientMap F A = 1 := (QuotientGroup.eq_one_iff _).mpr hA
  simp [hone] at horder

private theorem sl_trace_square (A : SpecialLinearGroup (Fin 2) F) :
    trace (A ^ 2).val = trace A.val ^ 2 - 2 := by
  change trace (A.val ^ 2) = _
  rw [sl_pow_two]
  simp [pow_two]

theorem projectiveTraceSquared_ne_square (hfive : (5 : F) ≠ 0)
    (x : Theory.PSL2.Group F) (hx : orderOf x = 5) :
    projectiveTraceSquared x ≠ projectiveTraceSquared (x ^ 2) := by
  obtain ⟨A, rfl⟩ := quotientMap_surjective F x
  rw [← map_pow, projectiveTraceSquared_mk, projectiveTraceSquared_mk, sl_trace_square]
  intro h
  have hp := trace_sq_polynomial_of_order_five A hx
  apply hfive
  linear_combination -(4 : F) * hp +
    (2 * trace A.val ^ 2 - 3) * (hp + h)

private theorem prime_field_aut_eq_refl [Finite F] {q : ℕ} (hq : q.Prime)
    (hF : Nat.card F = q) (σ : F ≃+* F) : σ = RingEquiv.refl F := by
  let : Fintype F := Fintype.ofFinite F
  let e : ZMod q ≃+* F := ZMod.ringEquivOfPrime F hq (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have h : e.trans σ = e := Subsingleton.elim _ _
  ext x
  have hh := RingEquiv.congr_fun h (e.symm x)
  simpa using hh

/-- Prime fields have no field automorphism contribution to the projective action. -/
theorem projectiveTraceSquared_aut_prime [Finite F] {q : ℕ} (hq : q.Prime)
    (hF : Nat.card F = q) (hchar : ringChar F ≠ 2) (hcard : 3 < Nat.card F)
    (α : MulAut (Theory.PSL2.Group F)) (x : Theory.PSL2.Group F) :
    projectiveTraceSquared (α x) = projectiveTraceSquared x := by
  obtain ⟨g, u, σ, rfl⟩ := odd_semilinear_coverage hchar hcard α
  rw [prime_field_aut_eq_refl hq hF σ]
  have hf : projectiveFieldAutHom (RingEquiv.refl F) = 1 := by
    exact projectiveFieldAutHom.map_one
  rw [hf, mul_one]
  change projectiveTraceSquared (g * diagonalAutHom u x * g⁻¹) = _
  rw [projectiveTraceSquared_conj, projectiveTraceSquared_diagonal]

end CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer
