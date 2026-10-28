module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag

/-!
# Fixed vectors of the natural binary line flag

The two line-radical translations and a cubic Levi element leave no
nonzero common fixed vector. Two upper triangular roots force every
Sylow fixed vector onto the first coordinate point. Every vector of that
point is an explicit displacement of the third coordinate by a line
translation. Only individual matrices and two field elements are reduced;
the vector arguments use their coordinates.

Source: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public section
open Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag

private theorem line_translation : Bruhat.upper 2 ∈ lineV := by decide +kernel
private def lineCubic : SL := ⟨!![0,1,0; 1,1,0; 0,0,1], by decide +kernel⟩
private theorem line_cubic : lineCubic ∈ lineA := by decide +kernel

/-- The line residual has no nonidentity fixed vector on its natural module. -/
theorem line_residual_fixed_eq_one (v : Model)
    (hv : ∀ a ∈ lineA, slAut a v = v) : v = 1 := by
  have ht := congrArg Multiplicative.toAdd (hv (Bruhat.upper 2)
    (show diagram (Bruhat.upper 2) ∈ pointA from pointV_le line_translation))
  have hc := congrArg Multiplicative.toAdd (hv lineCubic line_cubic)
  rw [slAut_apply] at ht hc
  change (!![0,1,0; 1,1,0; 0,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v.toAdd = v.toAdd at hc
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  have ht0 := congrFun ht 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hc0 hc1 ht0
  simp [Bruhat.upper] at hc0 hc1 ht0
  apply Multiplicative.toAdd.injective
  change v.toAdd = 0
  ext i
  fin_cases i <;> simp_all

/-- The common fixed vectors of the upper triangular Sylow lie on its point. -/
theorem borel_fixed_mem_point (v : Model)
    (hv : ∀ a ∈ borelSL, slAut a v = v) : v ∈ point := by
  have h1 := congrArg Multiplicative.toAdd (hv (Bruhat.upper 1) (Bruhat.upper_mem 1))
  have h4 := congrArg Multiplicative.toAdd (hv (Bruhat.upper 4) (Bruhat.upper_mem 4))
  rw [slAut_apply] at h1 h4
  have he1 := congrFun h1 0
  have he2 := congrFun h4 1
  simp [Bruhat.upper, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at he1 he2
  exact ⟨he1,he2⟩

/-- Every vector of the Sylow fixed line is a displacement by the line radical. -/
theorem point_displacement (v : Model) (hv : v ∈ point) :
    ∃ w : Model, ∃ a ∈ lineV, v = w * (slAut a w)⁻¹ := by
  refine ⟨Multiplicative.ofAdd ![0,0,v.toAdd 0], Bruhat.upper 2, line_translation, ?_⟩
  apply Multiplicative.toAdd.injective
  change v.toAdd = ![0,0,v.toAdd 0] +
    -((slAut (Bruhat.upper 2) (Multiplicative.ofAdd ![0,0,v.toAdd 0])).toAdd)
  rw [slAut_apply]
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  have hadd : ∀ a : ZMod 2, a + a = 0 := by decide
  ext i
  fin_cases i <;> simp [Bruhat.upper, hv.1, hv.2, hneg, hadd]

end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
