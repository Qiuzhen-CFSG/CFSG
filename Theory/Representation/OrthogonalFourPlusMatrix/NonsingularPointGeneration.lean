module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPoint
public import Mathlib.GroupTheory.Goursat
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
The stabilizer of an invertible matrix projects isomorphically onto either
special linear factor. Simplicity makes this graph maximal in the product.
Its fixed vectors form exactly the field line through the matrix, by the
scalar commutant of the transvections. Consequently two nonsingular vectors
on different field lines have point stabilizers generating the full product.

Source application: Aschbacher--Smith, 9.4.2, printed p.736.
-/

public section
open Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]

private theorem point_snd_surjective (v : Mat (F := F)) (hv : v.det ≠ 0) :
    Function.Surjective (Prod.snd ∘ (pointStabilizer v).subtype) := by
  intro b
  have hvv' : v⁻¹ * v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  let a : SpecialLinearGroup (Fin 2) F := ⟨v * b.val * v⁻¹, by
    rw [Matrix.det_mul, Matrix.det_mul, b.det_coe, mul_one, Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using mul_inv_cancel₀ hv⟩
  refine ⟨⟨(a,b),(mem_pointStabilizer_iff (a,b) v).mpr ?_⟩,rfl⟩
  change v * b.val * v⁻¹ * v = v * b.val
  simp only [mul_assoc,hvv',mul_one]

private theorem point_overgroup [IsSimpleGroup (SpecialLinearGroup (Fin 2) F)]
    (v : Mat (F := F)) (hv : v.det ≠ 0)
    (J : Subgroup (PairSL (F := F))) (hJ : pointStabilizer v ≤ J) :
    J = pointStabilizer v ∨ J = ⊤ := by
  have hfst : Function.Surjective (Prod.fst ∘ J.subtype) := by
    intro a
    obtain ⟨b,hb⟩ := (pointProjection_bijective v hv).2 a
    exact ⟨⟨b,hJ b.property⟩,hb⟩
  let : J.goursatFst.Normal := normal_goursatFst hfst
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J.goursatFst inferInstance with he | he
  · left
    apply le_antisymm ?_ hJ
    intro g hg
    obtain ⟨d,hd⟩ := point_snd_surjective v hv g.2
    have hmem : g.1 * d.val.1⁻¹ ∈ J.goursatFst := by
      rw [mem_goursatFst]
      convert J.mul_mem hg (J.inv_mem (hJ d.property)) using 1
      exact Prod.ext rfl (by change 1 = g.2 * d.val.2⁻¹; change d.val.2 = g.2 at hd; rw [hd,mul_inv_cancel])
    rw [he,mem_bot] at hmem
    have hgd : g = d.val := Prod.ext (mul_inv_eq_one.mp hmem) hd.symm
    exact hgd ▸ d.property
  · right
    apply top_unique
    intro g _
    obtain ⟨d,hd⟩ := point_snd_surjective v hv g.2
    have hm : (g.1 * d.val.1⁻¹,1) ∈ J :=
      mem_goursatFst.mp (he ▸ mem_top _)
    convert J.mul_mem hm (hJ d.property) using 1
    exact Prod.ext (by simp) (by change g.2 = 1 * d.val.2; rw [one_mul]; exact hd.symm)

/-- The fixed vectors of a nonsingular diagonal stabilizer are its field line. -/
theorem mem_span_of_pointStabilizer_le (v w : Mat (F := F)) (hv : v.det ≠ 0)
    (h : pointStabilizer v ≤ pointStabilizer w) :
    w ∈ Submodule.span F ({v} : Set (Mat (F := F))) := by
  have hvv : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
  have hvv' : v⁻¹ * v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  have hc (a : SpecialLinearGroup (Fin 2) F) : Commute a.val (w * v⁻¹) := by
    obtain ⟨d,hd⟩ := (pointProjection_bijective v hv).2 a
    have he := (mem_pointStabilizer_iff d.val v).mp d.property
    have hw := (mem_pointStabilizer_iff d.val w).mp (h d.property)
    change d.val.1 = a at hd
    rw [hd] at he hw
    have hb : d.val.2.val * v⁻¹ = v⁻¹ * a.val := by
      calc
        d.val.2.val * v⁻¹ = v⁻¹ * (v * d.val.2.val) * v⁻¹ := by
          simp only [←mul_assoc,hvv',one_mul]
        _ = v⁻¹ * (a.val * v) * v⁻¹ := by rw [he]
        _ = v⁻¹ * a.val := by simp only [mul_assoc,hvv,mul_one]
    change a.val * (w * v⁻¹) = w * v⁻¹ * a.val
    rw [←mul_assoc,hw,mul_assoc,hb,mul_assoc]
  obtain ⟨c,hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct
    (M := w * v⁻¹) (fun t => hc ⟨t.toMatrix,by simp⟩)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c,?_⟩
  calc
    c • v = Matrix.scalar (Fin 2) c * v := by
      ext i j
      rw [Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl
    _ = w * v⁻¹ * v := by rw [hc]
    _ = w := by rw [mul_assoc,hvv',mul_one]

/-- Distinct nonsingular field lines have stabilizers generating both factors. -/
theorem pointStabilizer_sup_eq_top [IsSimpleGroup (SpecialLinearGroup (Fin 2) F)]
    (v w : Mat (F := F)) (hv : v.det ≠ 0) (hw : w.det ≠ 0)
    (hne : w ∉ Submodule.span F ({v} : Set (Mat (F := F)))) :
    pointStabilizer v ⊔ pointStabilizer w = ⊤ := by
  rcases point_overgroup w hw (pointStabilizer v ⊔ pointStabilizer w) le_sup_right with he | he
  · exact (hne (mem_span_of_pointStabilizer_le v w hv (he ▸ le_sup_left))).elim
  · exact he

end ClassicalOrthogonal.FourPlusMatrix
