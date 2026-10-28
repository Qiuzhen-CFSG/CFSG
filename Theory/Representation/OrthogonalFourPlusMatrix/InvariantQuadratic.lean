module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary

/-!
# Invariant quadratic forms and linear involutions of the determinant normalizer

Over a field containing a scalar whose square differs from one, every
quadratic form invariant under the two SL₂ factors is a scalar multiple of
the determinant. A diagonal element forces the form to vanish on each row
space. A lower transvection makes the remaining pairing alternating, and
an alternating pairing on a two-dimensional space is a multiple of the wedge.

Consequently an F₄-linear involution in the full binary normalizer preserves
the F₄-valued determinant: its similitude multiplier squares to one and is
therefore one in characteristic two. No isometry premise is assumed.

Source application: Aschbacher--Smith 14.4.6(b), combined manuscript
(1 March 2004), printed p.1008.
-/

public section
open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]

private def row (i : Fin 2) : (Fin 2 → F) →ₗ[F] Mat (F := F) where
  toFun v j k := if j = i then v k else 0
  map_add' v w := by
    ext j k
    change (if j = i then (v + w) k else 0) =
      (if j = i then v k else 0) + (if j = i then w k else 0)
    by_cases h : j = i <;> simp [h]
  map_smul' c v := by
    ext j k
    change (if j = i then (c • v) k else 0) = c * (if j = i then v k else 0)
    by_cases h : j = i <;> simp [h]

@[simp] private lemma row_apply (i : Fin 2) (v : Fin 2 → F) (j k : Fin 2) :
    row i v j k = if j = i then v k else 0 := rfl


/-- Every invariant quadratic form is a multiple of the determinant. -/
theorem invariant_quadratic_eq_det (a : F) (ha : a ≠ 0) (ha2 : a * a ≠ 1)
    (q : QuadraticForm F (Mat (F := F)))
    (hq : ∀ g : PairSL (F := F), ∀ M, q (matrixAction g M) = q M) :
    ∃ c : F, ∀ M, q M = c * M.det := by
  have hr (i : Fin 2) (v : Fin 2 → F) : q (row i v) = 0 := by
    have hi : ∃ g : PairSL (F := F), matrixAction g (row i v) = a • row i v := by
      fin_cases i
      · refine ⟨(SpecialLinearGroup.diag2 a ha, 1), ?_⟩
        change (SpecialLinearGroup.diag2 a ha).val * row 0 v *
          (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = a • row 0 v
        rw [inv_one]
        change (SpecialLinearGroup.diag2 a ha).val * row 0 v * (1 : Mat) = a • row 0 v
        rw [mul_one, SpecialLinearGroup.diag2_coe']
        ext j k
        fin_cases j <;> fin_cases k <;>
          simp [Matrix.mul_apply]
      · refine ⟨(SpecialLinearGroup.diag2 a⁻¹ (inv_ne_zero ha), 1), ?_⟩
        change (SpecialLinearGroup.diag2 a⁻¹ (inv_ne_zero ha)).val * row 1 v *
          (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = a • row 1 v
        rw [inv_one]
        change (SpecialLinearGroup.diag2 a⁻¹ (inv_ne_zero ha)).val * row 1 v * (1 : Mat) =
          a • row 1 v
        rw [mul_one, SpecialLinearGroup.diag2_coe']
        ext j k
        fin_cases j <;> fin_cases k <;>
          simp [Matrix.mul_apply]
    obtain ⟨g, hg⟩ := hi
    have h := hq g (row i v)
    rw [hg, q.map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp (show (a * a - 1) * q (row i v) = 0 by
      linear_combination h)).resolve_left (sub_ne_zero.mpr ha2)
  let b : (Fin 2 → F) →ₗ[F] (Fin 2 → F) →ₗ[F] F :=
    q.polarBilin.compl₁₂ (row 0) (row 1)
  have hself (v : Fin 2 → F) : b v v = 0 := by
    have h := hq (SpecialLinearGroup.transvection one_ne_zero (1 : F), 1) (row 0 v)
    have he : matrixAction (SpecialLinearGroup.transvection one_ne_zero (1 : F), 1)
        (row 0 v) = row 0 v + row 1 v := by
      change (SpecialLinearGroup.transvection one_ne_zero (1 : F)).val * row 0 v *
        (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = row 0 v + row 1 v
      rw [inv_one]
      change (SpecialLinearGroup.transvection one_ne_zero (1 : F)).val * row 0 v *
        (1 : Mat) = row 0 v + row 1 v
      rw [mul_one, SpecialLinearGroup.transvection_coe]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply]
    rw [he, QuadraticMap.map_add q, hr, hr, zero_add, zero_add] at h
    exact h
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have hcross : b e1 e0 = -b e0 e1 := by
    have h := hself (e0 + e1)
    simp only [map_add, LinearMap.add_apply, hself, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hdecomp (v : Fin 2 → F) : v = v 0 • e0 + v 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  have hb (u v : Fin 2 → F) : b u v = (u 0 * v 1 - u 1 * v 0) * b e0 e1 := by
    conv_lhs => rw [hdecomp u, hdecomp v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hself, mul_zero, zero_add, add_zero, hcross]
    ring
  refine ⟨b e0 e1, fun M => ?_⟩
  have hM : M = row 0 (M 0) + row 1 (M 1) := by
    ext i j
    fin_cases i <;> simp
  have hqM : q M = b (M 0) (M 1) := by
    conv_lhs => rw [hM, QuadraticMap.map_add q, hr, hr, zero_add, zero_add]
    rfl
  rw [hqM, hb, Matrix.det_fin_two]
  ring
end ClassicalOrthogonal.FourPlusMatrix

namespace ClassicalOrthogonal.FourPlusMatrix.Binary

/-- An F₄-linear normalizer involution is an actual determinant isometry. -/
theorem field_involution_preserves_det (t : V ≃ₗ[F] V)
    (hn : t.restrictScalars (ZMod 2) ∈
      Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : ∀ M, t (t M) = M) : ∀ M, (t M).det = M.det := by
  let q : QuadraticForm F V := determinantForm.comp t.toLinearMap
  have hq (g : G) (M : V) : q (matrixAction g M) = q M := by
    obtain ⟨h, hh⟩ := (Subgroup.mem_normalizer_iff.mp hn (linearAction g)).mp ⟨g, rfl⟩
    have he (N : V) : t (action g N) = action h (t N) := by
      have hi := LinearEquiv.congr_fun hh (t N)
      simpa using hi.symm
    change determinantForm (t (action g M)) = determinantForm (t M)
    rw [he, determinantForm_apply, determinantForm_apply]
    exact matrixAction_det h (t M)
  obtain ⟨c, hc⟩ := invariant_quadratic_eq_det (QuadraticAlgebra.omega : F)
    (by decide +kernel) (by decide +kernel) q hq
  have hc' (M : V) : (t M).det = c * M.det := by
    have h := hc M
    change determinantForm (t M) = c * M.det at h
    rw [determinantForm_apply] at h
    exact h
  have hc1 : (t (1 : V)).det = c := by simpa using hc' 1
  have hcc : c * c = 1 := by
    have h := hc' (t 1)
    rw [h2, hc1, Matrix.det_one] at h
    exact h.symm
  have hc_eq : c = 1 := CharTwo.sq_injective (by simpa only [pow_two, one_mul] using hcc)
  intro M
  simpa only [hc_eq, one_mul] using hc' M
end ClassicalOrthogonal.FourPlusMatrix.Binary
