module
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionDisplacement

/-!
# Translations along a singular line through a nonsingular point

The fixed space of a nonidentity tensor involution equals its displacement
space. Polarization therefore vanishes on pairs of fixed vectors. Adding a
fixed singular vector to a fixed nonsingular vector preserves determinant.
The resulting translation is induced by the first special linear factor;
its matrix is `(v + z) v⁻¹`, and it fixes the singular direction `z`.

Source application: the point fusion in Aschbacher--Smith 9.4.1, p.736.
-/

public section
open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.PointLineTranslation

variable {F : Type*} [Field F]

private theorem det_add_of_fixed_displacement (g : PairSL (F := F))
    (v z a : Mat (F := F)) (hv : matrixAction g v = v)
    (ha : matrixAction g a - a = z) (hz : z.det = 0) : (v+z).det = v.det := by
  let B := (determinantForm (F := F)).polarBilin
  have he : B v (matrixAction g a) = B v a := by
    have hsum : (v + matrixAction g a).det = (v+a).det := by
      calc
        _ = (matrixAction g (v+a)).det := by rw [map_add,hv]
        _ = _ := matrixAction_det g (v+a)
    simp only [B,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      determinantForm_apply,hsum,matrixAction_det]
  have hB : B v z = 0 := by rw [←ha,map_sub,he,sub_self]
  change (determinantForm (F := F)).polarBilin v z = 0 at hB
  have h := QuadraticMap.map_add (determinantForm (F := F)) v z
  simp only [determinantForm_apply,←QuadraticMap.polarBilin_apply_apply] at h
  simpa only [hz,hB,add_zero] using h

theorem det_add_of_involution_fixed (g : Binary.G) (hg : g ≠ 1) (hg2 : g ^ 2 = 1)
    (v z : Binary.V) (hv : Binary.action g v = v) (hz : Binary.action g z = z)
    (hzdet : z.det = 0) : (v + z).det = v.det := by
  obtain ⟨a,ha⟩ := InvolutionDisplacement.exists_displacement_of_fixed g hg hg2 z hz
  exact det_add_of_fixed_displacement g v z a hv ha hzdet

private theorem square_zero_of_det (B : Mat (F := F))
    (hB : B.det = 0) (hB1 : (1+B).det = 1) : B*B=0 := by
  have ht : B 0 0 + B 1 1 = 0 := by
    simp [det_fin_two] at hB1
    have hd := hB
    rw [det_fin_two] at hd
    linear_combination hB1 - hd
  have hd := hB
  rw [det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.zero_apply]
  · change B 0 0 * B 0 0 + B 0 1 * B 1 0 = 0
    linear_combination B 0 0 * ht - hd
  · change B 0 0 * B 0 1 + B 0 1 * B 1 1 = 0
    linear_combination B 0 1 * ht
  · change B 1 0 * B 0 0 + B 1 1 * B 1 0 = 0
    linear_combination B 1 0 * ht
  · change B 1 0 * B 0 1 + B 1 1 * B 1 1 = 0
    linear_combination B 1 1 * ht - hd

/-- The first factor realizes a determinant-preserving singular translation. -/
theorem exists_first_translation (v z : Mat (F := F))
    (hv : v.det ≠ 0) (hz : z.det = 0) (hadd : (v+z).det=v.det) :
    ∃ a : SpecialLinearGroup (Fin 2) F,
      matrixAction (a,1) v = v+z ∧ matrixAction (a,1) z = z := by
  have hvv : v*v⁻¹=1 := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
  have hvv' : v⁻¹*v=1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  have he : 1 + z*v⁻¹ = (v+z)*v⁻¹ := by rw [add_mul,hvv]
  have hnil : (z*v⁻¹)*(z*v⁻¹)=0 := square_zero_of_det _
    (by rw [Matrix.det_mul,hz,zero_mul]) (by
      rw [he,Matrix.det_mul,hadd,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact mul_inv_cancel₀ hv)
  let a : SpecialLinearGroup (Fin 2) F := ⟨(v+z)*v⁻¹,by
    rw [Matrix.det_mul,hadd,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact mul_inv_cancel₀ hv⟩
  refine ⟨a,?_,?_⟩
  · change ((v+z)*v⁻¹)*v*(1:SpecialLinearGroup (Fin 2) F)⁻¹.val=v+z
    rw [inv_one,SpecialLinearGroup.coe_one,mul_one,mul_assoc,hvv',mul_one]
  · have hh : z*v⁻¹*z=0 := by
      have hh := congrArg (fun x : Mat (F := F) => x*v) hnil
      simpa only [mul_assoc,hvv',mul_one,zero_mul] using hh
    change ((v+z)*v⁻¹)*z*(1:SpecialLinearGroup (Fin 2) F)⁻¹.val=z
    rw [inv_one,SpecialLinearGroup.coe_one,mul_one,add_mul,add_mul,hvv,one_mul,hh,add_zero]

/-- A nonzero singular translation leaves the nonsingular point's field line. -/
theorem add_not_mem_span (v z : Mat (F := F))
    (hv : v.det ≠ 0) (hz : z.det = 0) (hz0 : z ≠ 0) :
    v+z ∉ Submodule.span F ({v} : Set (Mat (F := F))) := by
  intro h
  have hmem : z ∈ Submodule.span F ({v} : Set (Mat (F := F))) := by
    simpa only [add_sub_cancel_left] using
      (Submodule.span F ({v} : Set (Mat (F := F)))).sub_mem h
        (Submodule.subset_span (Set.mem_singleton v))
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := fun h => hz0 (by rw [←hc,h,zero_smul])
  have he := congrArg Matrix.det hc
  rw [Matrix.det_smul,Fintype.card_fin,hz] at he
  exact mul_ne_zero (pow_ne_zero _ hc0) hv he

end ClassicalOrthogonal.FourPlusMatrix.PointLineTranslation
