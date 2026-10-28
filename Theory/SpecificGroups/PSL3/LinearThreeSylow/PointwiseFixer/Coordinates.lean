module

public import Theory.SpecificGroups.PSL3.CartanActions.ResidualLinear
public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs

/-!
# Coordinate calculation for the PSL₃ Sylow pointwise fixer

Over a field of characteristic two, fixing the two simple root elements with
parameter one forces the linear factor to be scalar times a highest-root
element. Fixing the first simple root with arbitrary parameter then kills the
coefficient automorphism. The opposition case would force a zero row in an
invertible matrix. The proved standard factorization therefore identifies
every standard pointwise fixer with conjugation by the highest-root group.

Projective equality is lifted using trace one, retaining the genuine scalar
quotient. This local lifting argument follows `FieldComponentFixer`; the
unconditional automorphism coverage and Sylow transport are assembled in the
parent module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), especially (!) and (*) on p.247;
the matrix automorphisms are those of GLS3, Theorem 2.5.12 and §2.7,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.PointwiseFixer
variable {F : Type*} [Field F]

private theorem scalar_of_projective_eq (x y : SL(3,F))
    (h : (QuotientGroup.mk x : PSL(3,F)) = QuotientGroup.mk y) :
    ∃ r : F, x.val = r • y.val := by
  have hc : y⁻¹ * x ∈ Subgroup.center SL(3,F) := QuotientGroup.eq.mp h.symm
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem trace_transvection [CharP F 2] {i j : Fin 3} (hij : i ≠ j) (c : F) :
    Matrix.trace (SpecialLinearGroup.transvection hij c).val = 1 := by
  simp [SpecialLinearGroup.transvection_coe, Matrix.trace_add, hij, Matrix.trace_one]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination htwo

private theorem conjugate_transvection_eq [CharP F 2]
    (m : GL (Fin 3) F) {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (a b : F) (h : linearConj F m (rootElement hij a) = rootElement hkl b) :
    m.val * (1 + Matrix.single i j a) = (1 + Matrix.single k l b) * m.val := by
  obtain ⟨r, hr⟩ := scalar_of_projective_eq
    (linearConjSL F m (SpecialLinearGroup.transvection hij a))
    (SpecialLinearGroup.transvection hkl b) h
  have hv (x : SL(3,F)) : (linearConjSL F m x).val = m.val * x.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m x)
  have ht : Matrix.trace (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val = 1 := by
    rw [hv, Matrix.trace_mul_cycle, m.inv_val, one_mul, trace_transvection]
  rw [hr, Matrix.trace_smul, trace_transvection, smul_eq_mul, mul_one] at ht
  have he : (linearConjSL F m (SpecialLinearGroup.transvection hij a)).val =
      (SpecialLinearGroup.transvection hkl b).val := by simpa [ht] using hr
  have he' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M * m.val) he
  simpa only [hv, Matrix.mul_assoc, m.inv_val, mul_one,
    SpecialLinearGroup.transvection_coe] using he'

private theorem simple_root_mem_unipotent (c : F) :
    rootElement (show (0 : Fin 3) ≠ 1 by decide) c ∈ unipotent F ∧
    rootElement (show (1 : Fin 3) ≠ 2 by decide) c ∈ unipotent F := by
  constructor
  all_goals
    apply Subgroup.mem_map_of_mem (projection F)
    rw [mem_unipotentSL_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe]

private theorem linear_simple_ones_shape [CharP F 2] (m : GL (Fin 3) F)
    (h01 : linearConj F m (rootElement (show (0 : Fin 3) ≠ 1 by decide) 1) =
      rootElement (show (0 : Fin 3) ≠ 1 by decide) 1)
    (h12 : linearConj F m (rootElement (show (1 : Fin 3) ≠ 2 by decide) 1) =
      rootElement (show (1 : Fin 3) ≠ 2 by decide) 1) :
    m.val = !![m.val 0 0,0,m.val 0 2; 0,m.val 0 0,0; 0,0,m.val 0 0] := by
  have h1 := conjugate_transvection_eq m (show (0 : Fin 3) ≠ 1 by decide)
    (show (0 : Fin 3) ≠ 1 by decide) 1 1 h01
  have h2 := conjugate_transvection_eq m (show (1 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) 1 1 h12
  simp only [mul_add, add_mul, mul_one, one_mul, add_right_inj] at h1 h2
  have h10 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) h1
  have h20 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 1) h1
  have h12' := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 2) h1
  have hd1 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 1) h1
  have h01' := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 2) h2
  have h21 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 2) h2
  have hd2 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 1 2) h2
  simp [Matrix.mul_apply, Matrix.single_apply] at h10 h20 h12' hd1 h01' h21 hd2
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

private theorem not_linear_swaps_simple_ones [CharP F 2] (m : GL (Fin 3) F)
    (h01 : linearConj F m (rootElement (show (1 : Fin 3) ≠ 2 by decide) 1) =
      rootElement (show (0 : Fin 3) ≠ 1 by decide) 1)
    (h12 : linearConj F m (rootElement (show (0 : Fin 3) ≠ 1 by decide) 1) =
      rootElement (show (1 : Fin 3) ≠ 2 by decide) 1) : False := by
  have h1 := conjugate_transvection_eq m (show (1 : Fin 3) ≠ 2 by decide)
    (show (0 : Fin 3) ≠ 1 by decide) 1 1 h01
  have h2 := conjugate_transvection_eq m (show (0 : Fin 3) ≠ 1 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) 1 1 h12
  simp only [mul_add, add_mul, mul_one, one_mul, add_right_inj] at h1 h2
  have h20 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 1) h2
  have h21 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 2 2) h1
  have h22 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 1 2) h2
  simp [Matrix.mul_apply, Matrix.single_apply] at h20 h21 h22
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  apply hn
  simp [Matrix.det_fin_three, h20, h21, h22.symm]

private theorem linearConj_eq_of_scalar (m : GL (Fin 3) F) (u : SL(3,F))
    (c : F) (hm : m.val = c • u.val) :
    linearConj F m = MulAut.conj (projection F u) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := projection_surjective F x
  change projection F (linearConjSL F m y) = projection F (u * y * u⁻¹)
  congr 1
  apply Subtype.ext
  have hv : (linearConjSL F m y).val = m.val * y.val * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m y)
  rw [hv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  apply (Units.mul_left_inj m).mp
  rw [Matrix.mul_assoc, m.inv_val, mul_one]
  rw [hm]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hi : u⁻¹.val * u.val = 1 := congrArg Subtype.val (inv_mul_cancel u)
  rw [hi, mul_one]

private theorem linear_field_fixer [CharP F 2] (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ u ∈ unipotent F, (linearConj F m * fieldAction F σ) u = u) :
    ∃ z ∈ projectiveCenter F, linearConj F m * fieldAction F σ = MulAut.conj z := by
  have h01 (c : F) :
      linearConj F m (rootElement (show (0 : Fin 3) ≠ 1 by decide) (σ c)) =
        rootElement (show (0 : Fin 3) ≠ 1 by decide) c := by
    simpa only [MulAut.mul_apply, FieldComponentFixer.fieldAction_rootElement] using
      hfix _ (simple_root_mem_unipotent c).1
  have h12 : linearConj F m (rootElement (show (1 : Fin 3) ≠ 2 by decide) 1) =
      rootElement (show (1 : Fin 3) ≠ 2 by decide) 1 := by
    simpa only [MulAut.mul_apply, FieldComponentFixer.fieldAction_rootElement, map_one] using
      hfix _ (simple_root_mem_unipotent (1 : F)).2
  have hm := linear_simple_ones_shape m (by simpa using h01 1) h12
  have hc : m.val 0 0 ≠ 0 := by
    intro hz
    have hd : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
    apply hd
    rw [hm]
    simp [Matrix.det_fin_three, hz]
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro c
    have he := conjugate_transvection_eq m (show (0 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 1 by decide) (σ c) c (h01 c)
    simp only [mul_add, add_mul, mul_one, one_mul, add_right_inj] at he
    have hh := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 1) he
    rw [hm] at hh
    simp [Matrix.mul_apply, Matrix.single_apply] at hh
    exact mul_left_cancel₀ hc (hh.trans (mul_comm _ _))
  rw [hσ, map_one, mul_one]
  let u := specialLinear F ⟨0,0,m.val 0 2 / m.val 0 0⟩
  refine ⟨projective F ⟨0,0,m.val 0 2 / m.val 0 0⟩,
    (mem_projectiveCenter F _).mpr ⟨_,rfl⟩, ?_⟩
  apply linearConj_eq_of_scalar m u (m.val 0 0)
  change m.val = m.val 0 0 • matrix F ⟨0,0,m.val 0 2 / m.val 0 0⟩
  conv_lhs => rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, hc, mul_div_cancel₀]

/-- Within the standard automorphism group, pointwise fixation of the upper
unitriangular subgroup leaves precisely conjugation by its highest-root group. -/
theorem exists_projectiveCenter_of_mem_standard [CharP F 2]
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F)
    (hfix : ∀ u ∈ unipotent F, α u = u) :
    ∃ z ∈ projectiveCenter F, α = MulAut.conj z := by
  obtain ⟨m,σ,he | he⟩ := CartanActions.ResidualLinear.standard_opposition_factorization α hα
  · rw [he] at hfix ⊢
    exact linear_field_fixer m σ hfix
  · have h01 := hfix _ (simple_root_mem_unipotent (1 : F)).1
    have h12 := hfix _ (simple_root_mem_unipotent (1 : F)).2
    simp only [he, MulAut.mul_apply, oppositionGraph_rootElement,
      FieldComponentFixer.fieldAction_rootElement, CharTwo.neg_eq, map_one] at h01 h12
    exact False.elim (not_linear_swaps_simple_ones m h01 h12)

end Matrix.PSL3.LinearThree.PointwiseFixer
