module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Model
public import Theory.SpecificGroups.PSL3.FieldComponentFixer

/-!
# Coverage of the full Frobenius centralizer

Every automorphism of the actual PSL₃(4) has a linear–field–graph form. Its
field and graph factors commute with Frobenius, so centralizing Frobenius
forces the linear factor to do so as well. Trace on elementary matrices
removes the projective scalar ambiguity: the kernel of the linear action
consists of scalar matrices. Consequently Frobenius sends the conjugating
matrix to a scalar multiple of itself. Dividing by any nonzero entry makes
all entries fixed, hence binary. The descended matrix is invertible and its
binary determinant is one.

This proves that the previously constructed `(SL₃(2) ⋊ C₂) × C₂` model maps
onto the full automorphism centralizer. It supplies the coverage input to
the field Sylow assembly; no faithfulness premise is used.

The trace argument follows `PSL3.FieldComponentFixer`; coefficient descent
follows the fixed-matrix calculation in `FixedResiduals.ProjectiveField`.
Source: Aschbacher–Smith, `refs/quasithin.pdf`, field row 16.1.4(4), printed
p.1171, and the quaternion-placement application in 16.4.9(2), printed p.1192.
The concrete automorphism conventions are those of GLS3 §2.7.
-/

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
noncomputable section

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

private theorem trace_transvection {i j : Fin 3} (hij : i ≠ j) (c : F) :
    Matrix.trace (SpecialLinearGroup.transvection hij c).val = 1 := by
  simp [SpecialLinearGroup.transvection_coe, Matrix.trace_add, hij, Matrix.trace_one]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination htwo

private theorem conjugate_transvection_eq
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

private theorem matrix_scalar_of_fixes_roots
    (m : GL (Fin 3) F)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j),
      linearConj F m (rootElement hij 1) = rootElement hij 1) :
    m.val = Matrix.scalar (Fin 3) (m.val 0 0) := by
  have he (i j : Fin 3) (hij : i ≠ j) :
      m.val * Matrix.single i j 1 = Matrix.single i j 1 * m.val := by
    have hh := conjugate_transvection_eq m hij hij 1 1 (h i j hij)
    simpa only [mul_add, add_mul, mul_one, one_mul, add_right_inj] using hh
  have hz (k i : Fin 3) (hki : k ≠ i) : m.val k i = 0 := by
    obtain ⟨j, hij⟩ := exists_ne i
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M k j) (he i j hij.symm)
    simpa [Matrix.mul_apply, Matrix.single_apply, hki, Ne.symm hki] using hh
  have hd (i j : Fin 3) : m.val i i = m.val j j := by
    by_cases hij : i = j
    · subst j; rfl
    · have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) (he i j hij)
      simpa [Matrix.mul_apply, Matrix.single_apply] using hh
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.scalar] using hd i 0
  · simp [Matrix.scalar, hij, hz i j hij]

private theorem linear_kernel_scalar (A : GL (Fin 3) F) (h : linearConj F A = 1) :
    ∃ r : F, A.val = Matrix.scalar (Fin 3) r := by
  refine ⟨A.val 0 0, matrix_scalar_of_fixes_roots A ?_⟩
  intro i j hij
  rw [h]
  rfl

private theorem frobenius_linear (A : GL (Fin 3) F) :
    pslFrobenius * linearConj F A =
      linearConj F (GeneralLinearGroup.map fieldFrobenius.toRingHom A) * pslFrobenius := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, pslFrobenius_mk, linearConj_mk]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    have ht (x : SL) : SpecialLinearGroup.toGL (slFrobenius x) =
        GeneralLinearGroup.map fieldFrobenius.toRingHom (SpecialLinearGroup.toGL x) :=
      Units.ext rfl
    rw [ht, linearConjSL_toGL, map_mul, map_mul, map_inv, linearConjSL_toGL, ht]

private theorem frobenius_scalar (A : GL (Fin 3) F)
    (hc : Commute (linearConj F A) pslFrobenius) :
    ∃ r : F, (A.val.map fieldFrobenius) = r • A.val := by
  let B := GeneralLinearGroup.map fieldFrobenius.toRingHom A
  have he : linearConj F B = linearConj F A := by
    apply mul_right_cancel (b := pslFrobenius)
    exact (frobenius_linear A).symm.trans hc.eq.symm
  obtain ⟨r, hr⟩ := linear_kernel_scalar (A⁻¹ * B) (by rw [map_mul, map_inv, he, inv_mul_cancel])
  refine ⟨r, ?_⟩
  have hv := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => A.val * M) hr
  change A.val * (A.inv * B.val) = A.val * Matrix.scalar (Fin 3) r at hv
  rw [← Matrix.mul_assoc, A.val_inv, one_mul] at hv
  calc
    A.val.map fieldFrobenius = B.val := rfl
    _ = A.val * Matrix.scalar (Fin 3) r := hv
    _ = r • A.val := by ext i j; simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem linear_scalar (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) =
      QuotientGroup.mk x
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem exists_binary_of_fixed (x : F) (hx : x ^ 2 = x) :
    ∃ y : ZMod 2, binaryCast y = x := by
  rcases eq_zero_or_one_of_sq_eq_self hx with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

private theorem linear_binary (A : GL (Fin 3) F)
    (hc : Commute (linearConj F A) pslFrobenius) :
    ∃ x : Binary, linearConj F A = MulAut.conj (binaryProject x) := by
  classical
  obtain ⟨r, hr⟩ := frobenius_scalar A hc
  have hs (i j : Fin 3) : (A.val i j) ^ 2 = r * A.val i j :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hr
  have he : ∃ i j, A.val i j ≠ 0 := by
    by_contra! hn
    have hz : A.val = 0 := by ext i j; exact hn i j
    exact A.det_ne_zero (by rw [hz, Matrix.det_zero])
  obtain ⟨i, j, ha⟩ := he
  let a := A.val i j
  have hr0 : r ≠ 0 := by
    intro hz
    have hh : a ^ 2 = 0 := by simpa only [hz, zero_mul] using hs i j
    exact ha (eq_zero_of_pow_eq_zero hh)
  have hfix (k l : Fin 3) : (A.val k l / a) ^ 2 = A.val k l / a := by
    rw [div_pow, hs k l, hs i j, mul_div_mul_left _ _ hr0]
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun k l =>
    Classical.choose (exists_binary_of_fixed (A.val k l / a) (hfix k l))
  have hM (k l : Fin 3) : binaryCast (M k l) = A.val k l / a :=
    Classical.choose_spec (exists_binary_of_fixed (A.val k l / a) (hfix k l))
  have hmat : Matrix.map M binaryCast = a⁻¹ • A.val := by
    ext k l
    change binaryCast (M k l) = a⁻¹ * A.val k l
    simpa only [div_eq_mul_inv, mul_comm] using hM k l
  have hd0 : Matrix.det M ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hmat
    change (binaryCast.mapMatrix M).det = (a⁻¹ • A.val).det at hd
    rw [← binaryCast.map_det, hz, map_zero, Matrix.det_smul] at hd
    exact (mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha)) A.det_ne_zero) hd.symm
  have hd : Matrix.det M = 1 := by
    exact ((by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) _).resolve_left hd0
  let x : Binary := ⟨M, hd⟩
  let u : Fˣ := Units.mk0 a⁻¹ (inv_ne_zero ha)
  have hx : SpecialLinearGroup.toGL (SpecialLinearGroup.map binaryCast x) =
      GeneralLinearGroup.scalar (Fin 3) u * A := by
    apply Units.ext
    change Matrix.map M binaryCast = _
    rw [hmat]
    ext k l
    simp [GeneralLinearGroup.scalar, Matrix.diagonal_mul, u]
  refine ⟨x, ?_⟩
  change linearConj F A = MulAut.conj (QuotientGroup.mk (SpecialLinearGroup.map binaryCast x))
  rw [← linearConj_toGL, hx, map_mul, linear_scalar, one_mul]

private theorem coefficient_eq_one_or_frobenius (σ : F ≃+* F) :
    σ = 1 ∨ σ = fieldFrobenius := by
  classical
  have hs : fieldFrobenius ^ 2 = 1 := by
    ext x
    exact fieldFrobenius_involutive x
  have hn : fieldFrobenius ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (congrArg (fun τ : F ≃+* F => τ x) he)
  have ho : orderOf fieldFrobenius = 2 := orderOf_eq_prime hs hn
  have hm : σ ∈ zpowers fieldFrobenius := by
    rw [← PSL3.FieldComponentFixer.coefficient_fixer_eq_zpowers]
    intro x
    rcases eq_zero_or_one_of_sq_eq_self x.property with hx | hx
    · change σ x.val = x.val
      rw [hx, map_zero]
    · change σ x.val = x.val
      rw [hx, map_one]
  have hf : IsOfFinOrder fieldFrobenius :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hs⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hn' : n < 2 := by simpa only [Finset.mem_range, ho] using hn
  interval_cases n
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)

/-- Every coefficient action over GF(4) is one of the two marked field actions. -/
private theorem exists_fieldParameter (σ : F ≃+* F) :
    ∃ s : C2, PSL3.OuterSolvable.fieldAction F σ = Matrix.PSL3Four.fieldAction s := by
  rcases coefficient_eq_one_or_frobenius σ with rfl | rfl
  · exact ⟨1, by rw [map_one, map_one]⟩
  · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), by
      rw [fieldAction_generator, frobenius_eq_fieldAction]⟩

/-- The binary graph and field model covers the full Frobenius centralizer. -/
public theorem modelHom_surjective : Function.Surjective modelHom := by
  intro a
  obtain ⟨A, σ, t, ha⟩ := QuaternionPlacement.exists_standardForm a.val
  obtain ⟨s, hs⟩ := exists_fieldParameter σ
  have he : a.val = linearConj F A * Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t := by
    simpa only [standardForm, hs] using ha
  have hc : Commute a.val pslFrobenius := mem_centralizer_singleton_iff.mp a.property
  have ht : Commute (Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t) pslFrobenius :=
    ((Commute.refl pslFrobenius).pow_left s.toAdd.val).mul_left
      (graph_commute_frobenius.pow_left t.toAdd.val)
  have hA : Commute (linearConj F A) pslFrobenius := by
    have h := hc.mul_left ht.inv_left
    have hh : a.val * (Matrix.PSL3Four.fieldAction s *
        involutionHom (graph F) (graph_sq F) t)⁻¹ = linearConj F A := by
      rw [he]
      group
    rwa [hh] at h
  obtain ⟨x, hx⟩ := linear_binary A hA
  refine ⟨(⟨x, t⟩, s), Subtype.ext ?_⟩
  rw [modelHom_apply, he, hx]
  have hst : Commute (involutionHom (graph F) (graph_sq F) t)
      (Matrix.PSL3Four.fieldAction s) :=
    (graph_commute_frobenius.pow_left t.toAdd.val).pow_right s.toAdd.val
  simpa only [mul_assoc] using congrArg (MulAut.conj (binaryProject x) * ·) hst.eq

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
