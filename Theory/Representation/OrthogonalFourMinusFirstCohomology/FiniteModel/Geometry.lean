module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Minus type of the finite Hermitian determinant form

The determinant form on the four-dimensional Hermitian space has nonsingular
polar form and Witt index one over the actual Frobenius fixed field.

For nonsingularity, the two diagonal vectors detect the diagonal coordinates.
The quadratic extension has a nonfixed element `t`, and the norm polar evaluated
at `z` and `z*t` is `norm(z) * (t + conjugation(t))`, which detects nonzero `z`.
For the Witt bound, project a totally singular subspace onto its second diagonal
coordinate. Anisotropy of the norm forces the kernel onto the first diagonal
line. A nonzero kernel vector then forces the whole subspace onto that line by
polar orthogonality; otherwise the projection is injective. The first diagonal
line itself attains dimension one.

This supplies the quadratic geometry of the orthogonal module in
Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419).
-/

public section

noncomputable section
namespace Representation.OrthogonalFourMinus.FiniteModel
variable (n : ℕ) [NeZero n]

/-- Conjugation on the quadratic extension is nontrivial. -/
lemma exists_conjugation_ne : ∃ t : Field n, conjugation n t ≠ t := by
  by_contra! h
  have hb : Function.Bijective (algebraMap (fixedField n) (Field n)) := by
    refine ⟨FaithfulSMul.algebraMap_injective _ _, ?_⟩
    intro t
    exact ⟨⟨t, h t⟩, rfl⟩
  have he := Module.finrank_of_bijective_algebraMap hb
  rw [finrank_field] at he
  contradiction

/-- The determinant in the coordinates of an arbitrary Hermitian matrix. -/
lemma form_eq_coordinates (v : Space n) :
    form n v = (coordinates n v).1.1 * (coordinates n v).1.2 - norm n (coordinates n v).2 := by
  simpa only [LinearEquiv.symm_apply_apply] using form_coordinates n (coordinates n v)

/-- The polar form in coordinates, after inclusion into the extension field. -/
lemma coe_polar_coordinates (v w : Space n) :
    ((form n).polarBilin v w : Field n) =
    (coordinates n v).1.1.val * (coordinates n w).1.2.val +
    (coordinates n v).1.2.val * (coordinates n w).1.1.val -
    ((coordinates n v).2 * conjugation n (coordinates n w).2 +
      (coordinates n w).2 * conjugation n (coordinates n v).2) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    form_eq_coordinates, map_add, Prod.fst_add, Prod.snd_add,
    Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_add, norm]
  ring

/-- The determinant has nonsingular polar form, including in characteristic two. -/
theorem form_nonsingular : (form n).polarBilin.Nondegenerate := by
  have hs : (form n).polarBilin.SeparatingLeft := by
    intro v hv
    have h1 := congrArg Subtype.val (hv ((coordinates n).symm ((1,0),0)))
    have h2 := congrArg Subtype.val (hv ((coordinates n).symm ((0,1),0)))
    rw [coe_polar_coordinates] at h1 h2
    have hb : (coordinates n v).1.2 = 0 := by
      apply Subtype.ext
      simpa using h1
    have ha : (coordinates n v).1.1 = 0 := by
      apply Subtype.ext
      simpa using h2
    have hz : (coordinates n v).2 = 0 := by
      by_contra hz
      obtain ⟨t, ht⟩ := exists_conjugation_ne n
      have hp := congrArg Subtype.val
        (hv ((coordinates n).symm ((0,0), (coordinates n v).2 * t)))
      rw [coe_polar_coordinates] at hp
      simp only [LinearEquiv.apply_symm_apply, Subfield.coe_zero, mul_zero,
        add_zero, zero_sub, map_mul, neg_eq_zero] at hp
      have he : (coordinates n v).2 * conjugation n (coordinates n v).2 *
          (conjugation n t + t) = 0 := by linear_combination hp
      have hc : conjugation n (coordinates n v).2 ≠ 0 :=
        (map_ne_zero (conjugation n)).mpr hz
      have ht' := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hz hc)
      exact ht (CharTwo.add_eq_zero.mp ht')
    apply (coordinates n).injective
    rw [map_zero]
    exact Prod.ext (Prod.ext ha hb) hz
  refine ⟨hs, ?_⟩
  intro v hv
  apply hs v
  intro w
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hv w

/-- Every totally singular subspace of the Hermitian determinant has dimension at most one. -/
theorem singular_finrank_le_one (W : Submodule (fixedField n) (Space n))
    (hW : ∀ v ∈ W, form n v = 0) : Module.finrank (fixedField n) W ≤ 1 := by
  classical
  let y : W →ₗ[fixedField n] fixedField n :=
    { toFun := fun w => (coordinates n w.val).1.2
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hz (w : W) (hw : y w = 0) : (coordinates n w.val).2 = 0 := by
    apply (norm_eq_zero_iff n _).mp
    have he := hW w.val w.property
    rw [form_eq_coordinates] at he
    change (coordinates n w.val).1.2 = 0 at hw
    simpa [hw] using he
  by_cases hy : ∀ w : W, y w = 0 → w = 0
  · have hi : Function.Injective y := by
      intro v w h
      apply sub_eq_zero.mp
      apply hy
      rw [map_sub, h, sub_self]
    simpa using LinearMap.finrank_le_finrank_of_injective hi
  · push Not at hy
    obtain ⟨w, hw, hw0⟩ := hy
    have hwb : (coordinates n w.val).1.2 = 0 := hw
    have hwz := hz w hw
    have hwa : (coordinates n w.val).1.1 ≠ 0 := by
      intro ha
      apply hw0
      apply Subtype.ext
      apply (coordinates n).injective
      simp only [Submodule.coe_zero, map_zero]
      exact Prod.ext (Prod.ext ha hwb) hwz
    have hall (v : W) : y v = 0 := by
      have hp : (form n).polarBilin w.val v.val = 0 := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
          hW _ (W.add_mem w.property v.property), hW _ w.property, hW _ v.property]
        simp
      have he := congrArg Subtype.val hp
      rw [coe_polar_coordinates] at he
      have he' : (coordinates n w.val).1.1 * (coordinates n v.val).1.2 = 0 := by
        apply Subtype.ext
        simpa [hwb, hwz] using he
      exact (mul_eq_zero.mp he').resolve_left hwa
    let x : W →ₗ[fixedField n] fixedField n :=
      { toFun := fun w => (coordinates n w.val).1.1
        map_add' := by intros; simp
        map_smul' := by intros; simp }
    have hx0 (v : W) (hv : x v = 0) : v = 0 := by
      apply Subtype.ext
      apply (coordinates n).injective
      simp only [Submodule.coe_zero, map_zero]
      exact Prod.ext (Prod.ext hv (hall v)) (hz v (hall v))
    have hx : Function.Injective x := by
      intro v w h
      apply sub_eq_zero.mp
      apply hx0
      rw [map_sub, h, sub_self]
    simpa using LinearMap.finrank_le_finrank_of_injective hx

/-- The first diagonal line is totally singular and has dimension one. -/
theorem exists_singular_line :
    ∃ W : Submodule (fixedField n) (Space n),
      Module.finrank (fixedField n) W = 1 ∧ ∀ v ∈ W, form n v = 0 := by
  let e : Space n := (coordinates n).symm ((1,0),0)
  have he : e ≠ 0 := by
    intro h
    have hc := congrArg (fun v => (coordinates n v).1.1) h
    simp [e] at hc
  refine ⟨Submodule.span (fixedField n) {e}, finrank_span_singleton he, ?_⟩
  intro v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [QuadraticMap.map_smul]
  have hq : form n e = 0 := by
    rw [form_coordinates]
    simp
  rw [hq, smul_zero]

end Representation.OrthogonalFourMinus.FiniteModel
