module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.Normalizer
public import Mathlib.Algebra.CharP.Reduced
/-!
# The actual two-by-two block of a parabolic conjugation

Conjugation by a parabolic GL₃ matrix preserves the literal local subgroup.
Taking its marked two-by-two block in the identity `g*x = conjugate(x)*g`
gives an intertwining identity for the original SL₂ quotient map. Over a
finite field of characteristic two, rescale the GL₂ block by a square root
of its determinant to obtain a determinant-one conjugating matrix.

Source: the local semilinear calculation in Aschbacher–Smith F.1.12,
printed p.264 (PDF p.275).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
variable (F : Type*) [Field F]
private theorem linearConjSL_val (g : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F g x).val = g.val * x.val * (g⁻¹).val :=
  congrArg Units.val (linearConjSL_toGL F g x)

/-- Parabolic conjugation preserves the literal vector or covector stabilizer. -/
theorem linear_mem_localSL (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hgi : ParabolicShape F point g⁻¹)
    (x : localSL F point) : linearConjSL F g x.val ∈ localSL F point := by
  cases point
  · obtain ⟨g20,g21⟩ := hg
    obtain ⟨i20,i21⟩ := hgi
    have hx := (mem_lineLocalSL_iff F x.val).mp x.property
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 2 2) g.val_inv
    change (g.val * (g⁻¹).val) 2 2 = 1 at he
    simp only [Matrix.mul_apply, Fin.sum_univ_three,g20,g21,zero_mul,zero_add] at he
    apply (mem_lineLocalSL_iff F _).mpr
    rw [linearConjSL_val]
    simp [-Matrix.coe_units_inv, Matrix.mul_apply, Fin.sum_univ_three,
      g20,g21,i20,i21,hx.1,hx.2.1,hx.2.2,he]
  · obtain ⟨g10,g20⟩ := hg
    obtain ⟨i10,i20⟩ := hgi
    have hx := (mem_pointLocalSL_iff F x.val).mp x.property
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) g.val_inv
    change (g.val * (g⁻¹).val) 0 0 = 1 at he
    simp only [Matrix.mul_apply, Fin.sum_univ_three,i10,i20,mul_zero,add_zero] at he
    apply (mem_pointLocalSL_iff F _).mpr
    rw [linearConjSL_val]
    simp [-Matrix.coe_units_inv, Matrix.mul_apply, Fin.sum_univ_three,
      g10,g20,i10,i20,hx.1,hx.2.1,hx.2.2,he]

def linearLocalSL (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hgi : ParabolicShape F point g⁻¹) :
    localSL F point →* localSL F point :=
  ((linearConjSL F g).toMonoidHom.comp (localSL F point).subtype).codRestrict _
    (linear_mem_localSL F point g hg hgi)

/-- The marked matrix block, before imposing determinant one. -/
def blockEntries (point : Bool) (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  if point then !![M 1 1,M 1 2; M 2 1,M 2 2] else !![M 0 0,M 0 1;M 1 0,M 1 1]

private theorem blockEntries_det_ne_zero (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) : (blockEntries F point g.val).det ≠ 0 := by
  have hn := GeneralLinearGroup.det_ne_zero g
  cases point
  · obtain ⟨h20,h21⟩ := hg
    have he : g.val.det = (blockEntries F false g.val).det * g.val 2 2 := by
      simp [blockEntries, det_fin_two, det_fin_three,h20,h21]
      ring
    rw [he] at hn
    exact (mul_ne_zero_iff.mp hn).1
  · obtain ⟨h10,h20⟩ := hg
    have he : g.val.det = g.val 0 0 * (blockEntries F true g.val).det := by
      simp [blockEntries, det_fin_two, det_fin_three,h10,h20]
      ring
    rw [he] at hn
    exact (mul_ne_zero_iff.mp hn).2

variable [Finite F] [CharP F 2]

theorem slBlock_entries (point : Bool) (x : localSL F point) :
    (slBlock F point x).val = blockEntries F point x.val.val := by
  cases point
  · exact slBlock_line_val F x
  · exact slBlock_point_val F x

private theorem block_intertwines (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hgi : ParabolicShape F point g⁻¹)
    (x : localSL F point) :
    blockEntries F point g.val * (slBlock F point x).val =
      (slBlock F point (linearLocalSL F point g hg hgi x)).val * blockEntries F point g.val := by
  let y := linearLocalSL F point g hg hgi x
  have he : g.val * x.val.val = y.val.val * g.val := by
    change _ = (linearConjSL F g x.val).val * g.val
    rw [linearConjSL_val, Matrix.mul_assoc]
    change _ = g.val * x.val.val * (g.inv * g.val)
    rw [g.inv_val,mul_one]
  change blockEntries F point g.val * (slBlock F point x).val =
    (slBlock F point y).val * blockEntries F point g.val
  rw [slBlock_entries,slBlock_entries]
  cases point
  · obtain ⟨g20,g21⟩ := hg
    have hx := (mem_lineLocalSL_iff F x.val).mp x.property
    ext i j
    have hh := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m i.castSucc j.castSucc) he
    fin_cases i <;> fin_cases j <;>
      simpa [blockEntries,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,
        hx.1,hx.2.1,g20,g21] using hh
  · obtain ⟨g10,g20⟩ := hg
    have hy := (mem_pointLocalSL_iff F y.val).mp y.property
    ext i j
    have hh := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m i.succ j.succ) he
    fin_cases i <;> fin_cases j <;>
      simpa [blockEntries,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,
        hy.2.1,hy.2.2,g10,g20] using hh

/-- The actual block action is conjugation by a determinant-one scalar multiple
of the original GL₂ block. -/
theorem linear_block_inner (point : Bool) (g : GL (Fin 3) F)
    (hg : ParabolicShape F point g) (hgi : ParabolicShape F point g⁻¹) :
    ∃ c : SL(2,F), ∀ x : localSL F point,
      slBlock F point (linearLocalSL F point g hg hgi x) = MulAut.conj c (slBlock F point x) := by
  let B := blockEntries F point g.val
  obtain ⟨r,hr⟩ := isSquare_of_charTwo' B.det
  have hn : r ≠ 0 := by
    intro h
    have hb := blockEntries_det_ne_zero F point g hg
    apply hb
    simpa [h] using hr
  let c : SL(2,F) := ⟨r⁻¹ • B, by
    rw [Matrix.det_smul, Fintype.card_fin,hr]
    simp [pow_two, ← mul_assoc, hn]⟩
  refine ⟨c, fun x => ?_⟩
  have he : c * slBlock F point x = slBlock F point (linearLocalSL F point g hg hgi x) * c := by
    apply Subtype.ext
    change (r⁻¹ • B) * (slBlock F point x).val =
      (slBlock F point (linearLocalSL F point g hg hgi x)).val * (r⁻¹ • B)
    rw [Matrix.smul_mul, Matrix.mul_smul]
    exact congrArg (r⁻¹ • ·) (block_intertwines F point g hg hgi x)
  change _ = c * slBlock F point x * c⁻¹
  rw [he,mul_inv_cancel_right]
end Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
