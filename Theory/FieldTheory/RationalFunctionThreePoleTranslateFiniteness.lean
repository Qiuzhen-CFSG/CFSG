module

public import Theory.FieldTheory.RationalFunctionProjectivePoles

/-!
# Finiteness of affine translates for rational functions with three poles

Let `t : k(X)` have at least three points in its projective pole support.  This
module proves that only finitely many constants `c : k` can occur in an
identity `sigma t = t + c` with `sigma` a `k`-automorphism of `k(X)`.  This is
the three-or-more-boundary-point branch of the rational-function form of
Borel, *Linear Algebraic Groups*, Theorems 10.8 and 10.9, as transcribed in
`refs/KGroup/Bor1/Chapter3.tex`.

The proof combines the Mobius classification from
`Theory.FieldTheory.RationalFunctionMobius` with pole-support covariance from
`Theory.FieldTheory.RationalFunctionProjectivePoles`.  Constant translation
preserves the finite pole support, so a matrix representing each witnessing
automorphism permutes it.  After choosing three distinct poles, send a
translation parameter to the ordered triple of their images, which lies in a
finite product of the pole support.

The key injectivity step is the direct fractional-linear version of Borel
10.8.  If two matrices agree on three distinct projective points, their
quotient fixes those points.  Mathlib's quadratic `fixpointPolynomial` then
vanishes: either it has three distinct affine roots, or fixing infinity lowers
its degree and it has two distinct affine roots.  The quotient is therefore
scalar, so the two Mobius rational functions, and hence the two automorphisms,
coincide.  Finally one automorphism cannot witness two constants because the
constant embedding into `k(X)` is injective.  The construction stays entirely
in field theory and has no algebraic-group dependency.
-/

universe u

open Polynomial
open scoped OnePoint

namespace RatFunc

variable {k : Type u} [Field k]

noncomputable section

local instance : DecidableEq k := Classical.decEq k

private lemma fixed_infty_two_affine_scalar
    (q : GL (Fin 2) k) (a b : k) (hab : a ≠ b)
    (hinfty : q • (OnePoint.infty : OnePoint k) = OnePoint.infty)
    (ha : q • (a : OnePoint k) = a) (hb : q • (b : OnePoint k) = b) :
    q.val ∈ Set.range (Matrix.scalar (Fin 2)) := by
  apply Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      q.fixpointPolynomial (f := ![a, b])
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr ha
    · exact Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hb
  · have hq10 : q 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hinfty
    simp only [Matrix.GeneralLinearGroup.fixpointPolynomial, hq10, map_zero, zero_mul,
      zero_add]
    (compute_degree; norm_num)

private lemma fixed_three_affine_scalar
    (q : GL (Fin 2) k) (a b c : k)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : q • (a : OnePoint k) = a) (hb : q • (b : OnePoint k) = b)
    (hc : q • (c : OnePoint k) = c) :
    q.val ∈ Set.range (Matrix.scalar (Fin 2)) := by
  apply Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      q.fixpointPolynomial (f := ![a, b, c])
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr ha
    · exact Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hb
    · exact Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hc
  · simp only [Matrix.GeneralLinearGroup.fixpointPolynomial]
    (compute_degree; norm_num)

private lemma fixed_three_projective_scalar
    (q : GL (Fin 2) k) (x y z : OnePoint k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : q • x = x) (hy : q • y = y) (hz : q • z = z) :
    q.val ∈ Set.range (Matrix.scalar (Fin 2)) := by
  cases x with
  | infty =>
      cases y with
      | infty => exact (hxy rfl).elim
      | coe b =>
          cases z with
          | infty => exact (hxz rfl).elim
          | coe c =>
              apply fixed_infty_two_affine_scalar q b c
              · simpa using hyz
              · exact hx
              · exact hy
              · exact hz
  | coe a =>
      cases y with
      | infty =>
          cases z with
          | infty => exact (hyz rfl).elim
          | coe c =>
              apply fixed_infty_two_affine_scalar q a c
              · simpa using hxz
              · exact hy
              · exact hx
              · exact hz
      | coe b =>
          cases z with
          | infty =>
              apply fixed_infty_two_affine_scalar q a b
              · simpa using hxy
              · exact hz
              · exact hx
              · exact hy
          | coe c =>
              apply fixed_three_affine_scalar q a b c
              · simpa using hxy
              · simpa using hxz
              · simpa using hyz
              · exact hx
              · exact hy
              · exact hz

private lemma quotient_fixes_of_smul_eq (g h : GL (Fin 2) k) (x : OnePoint k)
    (hx : g • x = h • x) : (h⁻¹ * g) • x = x := by
  rw [mul_smul, hx, inv_smul_smul]

private lemma mobius_eq_of_three_projective_values
    (g h : GL (Fin 2) k) (x y z : OnePoint k)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : g • x = h • x) (hy : g • y = h • y) (hz : g • z = h • z) :
    (C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1)) =
      (C (h 0 0) * X + C (h 0 1)) / (C (h 1 0) * X + C (h 1 1)) := by
  let q := h⁻¹ * g
  have hscalar : q.val ∈ Set.range (Matrix.scalar (Fin 2)) :=
    fixed_three_projective_scalar q x y z hxy hxz hyz
      (quotient_fixes_of_smul_eq g h x hx)
      (quotient_fixes_of_smul_eq g h y hy)
      (quotient_fixes_of_smul_eq g h z hz)
  obtain ⟨a, ha⟩ := hscalar
  have ha0 : a ≠ 0 := by
    intro ha0
    apply q.det_ne_zero
    rw [← ha, ha0]
    simp
  let scalarUnit : kˣ := Units.mk0 a ha0
  have hq : q = Matrix.GeneralLinearGroup.scalar (Fin 2) scalarUnit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    simpa [scalarUnit] using ha.symm
  have hg : g = h * Matrix.GeneralLinearGroup.scalar (Fin 2) scalarUnit := by
    calc
      g = h * q := by simp [q]
      _ = h * Matrix.GeneralLinearGroup.scalar (Fin 2) scalarUnit := by rw [hq]
  have hgij (i j : Fin 2) : g i j = h i j * a := by
    rw [hg]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, scalarUnit]
  rw [hgij 0 0, hgij 0 1, hgij 1 0, hgij 1 1]
  have hnum :
      C (h 0 0 * a) * X + C (h 0 1 * a) =
        C a * (C (h 0 0) * X + C (h 0 1)) := by
    simp only [map_mul]
    ring
  have hden :
      C (h 1 0 * a) * X + C (h 1 1 * a) =
        C a * (C (h 1 0) * X + C (h 1 1)) := by
    simp only [map_mul]
    ring
  have hCa : C a ≠ (0 : RatFunc k) := by
    intro hzero
    apply ha0
    apply (C : k →+* RatFunc k).injective
    simpa using hzero
  rw [hnum, hden, mul_div_mul_left _ _ hCa]

/-- A rational function with at least three projective poles has only finitely
many constant translates in its orbit under `k`-automorphisms of `k(X)`. -/
public theorem finite_affine_translate_parameters_of_three_le_ncard
    [IsAlgClosed k] (t : RatFunc k) (hthree : 3 ≤ t.projectivePoleSupport.ncard) :
    {c : k | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
      sigma t = t + algebraMap k (RatFunc k) c}.Finite := by
  let parameters : Set k := {c | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
    sigma t = t + algebraMap k (RatFunc k) c}
  let sigma : parameters → RatFunc k ≃ₐ[k] RatFunc k := fun c ↦ c.property.choose
  have hsigma (c : parameters) : sigma c t = t + C (c : k) :=
    c.property.choose_spec
  let matrix : parameters → GL (Fin 2) k :=
    fun c ↦ (algEquiv_X_eq_mobius (sigma c)).choose
  have hmatrix (c : parameters) : sigma c (X : RatFunc k) =
      (C (matrix c 0 0) * X + C (matrix c 0 1)) /
        (C (matrix c 1 0) * X + C (matrix c 1 1)) :=
    (algEquiv_X_eq_mobius (sigma c)).choose_spec
  have hmaps (c : parameters) (w : OnePoint k) (hw : w ∈ t.projectivePoleSupport) :
      projectiveLinearAction (matrix c) w ∈ t.projectivePoleSupport := by
    have hcov := projectivePoleSupport_algEquiv (sigma c) t (matrix c) (hmatrix c)
    rw [hsigma c, projectivePoleSupport_add_C] at hcov
    rw [hcov] at hw
    exact hw
  obtain ⟨triple, htriple, htripleCard⟩ := Set.exists_subset_card_eq hthree
  obtain ⟨x, y, z, hxy, hxz, hyz, htripleEq⟩ :=
    Set.ncard_eq_three.mp htripleCard
  have hxSupport : x ∈ t.projectivePoleSupport := htriple (by simp [htripleEq])
  have hySupport : y ∈ t.projectivePoleSupport := htriple (by simp [htripleEq])
  have hzSupport : z ∈ t.projectivePoleSupport := htriple (by simp [htripleEq])
  let support := {w // w ∈ t.projectivePoleSupport}
  let signature : parameters → support × support × support := fun c ↦
    ⟨⟨projectiveLinearAction (matrix c) x, hmaps c x hxSupport⟩,
      ⟨⟨projectiveLinearAction (matrix c) y, hmaps c y hySupport⟩,
        ⟨projectiveLinearAction (matrix c) z, hmaps c z hzSupport⟩⟩⟩
  have signature_injective : Function.Injective signature := by
    intro c d hcd
    have hx : projectiveLinearAction (matrix c) x =
        projectiveLinearAction (matrix d) x := congrArg (fun q ↦ q.1.val) hcd
    have hy : projectiveLinearAction (matrix c) y =
        projectiveLinearAction (matrix d) y := congrArg (fun q ↦ q.2.1.val) hcd
    have hz : projectiveLinearAction (matrix c) z =
        projectiveLinearAction (matrix d) z := congrArg (fun q ↦ q.2.2.val) hcd
    have hx' : matrix c • x = matrix d • x := by
      simpa only [projectiveLinearAction_eq_smul] using hx
    have hy' : matrix c • y = matrix d • y := by
      simpa only [projectiveLinearAction_eq_smul] using hy
    have hz' : matrix c • z = matrix d • z := by
      simpa only [projectiveLinearAction_eq_smul] using hz
    have hmobius := mobius_eq_of_three_projective_values
      (matrix c) (matrix d) x y z hxy hxz hyz hx' hy' hz'
    have hsigmaEq : sigma c = sigma d := by
      apply algEquiv_ext_X
      calc
        sigma c (X : RatFunc k) =
            (C (matrix c 0 0) * X + C (matrix c 0 1)) /
              (C (matrix c 1 0) * X + C (matrix c 1 1)) := hmatrix c
        _ = (C (matrix d 0 0) * X + C (matrix d 0 1)) /
              (C (matrix d 1 0) * X + C (matrix d 1 1)) := hmobius
        _ = sigma d (X : RatFunc k) := (hmatrix d).symm
    apply Subtype.ext
    apply (C : k →+* RatFunc k).injective
    apply add_left_cancel (a := t)
    rw [← hsigma c, ← hsigma d, hsigmaEq]
  let _ : Finite support := (projectivePoleSupport_finite t).to_subtype
  let _ : Finite parameters := Finite.of_injective signature signature_injective
  simpa [parameters] using (Set.toFinite parameters)

end


end RatFunc
