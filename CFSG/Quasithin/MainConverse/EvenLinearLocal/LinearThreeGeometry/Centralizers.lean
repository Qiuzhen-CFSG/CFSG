module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.RootPlanes
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
public import CFSG.Quasithin.Defs

/-!
# Characteristic two of the full degree-three parabolics

Centralizing either root plane forces a matrix to be a scalar times a member
of that plane. Projective centralization lifts to matrix centralization by
trace invariance. Thus the projective root planes are self-centralizing.
They are normal two-subgroups of the full parabolics, so their containment
in the intrinsic two-cores proves C_P(O₂(P)) ≤ O₂(P).

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, repeated on p.482.
These are full-parabolic assertions, including their diagonal elements.
-/

public section
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.RootPlaneGeometry
namespace CFSG.Quasithin.MainConverse.LinearThreeGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem projective_eq_of_scalar (g u : SL(3,F)) (r : F)
    (he : g.val = r • u.val) : projection F g = projection F u := by
  apply (projection F).eq_iff.mpr
  rw [projection_ker, Subgroup.mem_center_iff]
  have hi : u⁻¹.val * u.val = 1 := congrArg Subtype.val (inv_mul_cancel u)
  have hv : (u⁻¹*g).val = r • (1 : Matrix (Fin 3) (Fin 3) F) := by
    change u⁻¹.val * g.val = _
    rw [he, Matrix.mul_smul, hi]
  intro b
  apply Subtype.ext
  change b.val * (u⁻¹*g).val = (u⁻¹*g).val * b.val
  rw [hv]
  simp

omit [Finite F] [CharP F 2] in
private theorem point_centralizer_projective (g : SL(3,F))
    (hc : ∀ a c : F, specialLinear F ⟨a,0,c⟩ * g = g * specialLinear F ⟨a,0,c⟩) :
    projection F g ∈ rootPlane F true := by
  have h10 := congrArg (fun h : SL(3,F) => h.val 0 0) (hc 1 0)
  have h20 := congrArg (fun h : SL(3,F) => h.val 0 0) (hc 0 1)
  have h12 := congrArg (fun h : SL(3,F) => h.val 0 2) (hc 1 0)
  have h21 := congrArg (fun h : SL(3,F) => h.val 0 1) (hc 0 1)
  have h11 := congrArg (fun h : SL(3,F) => h.val 0 1) (hc 1 0)
  have h22 := congrArg (fun h : SL(3,F) => h.val 0 2) (hc 0 1)
  change (matrix F ⟨1,0,0⟩ * g.val) 0 0 = (g.val * matrix F ⟨1,0,0⟩) 0 0 at h10
  change (matrix F ⟨0,0,1⟩ * g.val) 0 0 = (g.val * matrix F ⟨0,0,1⟩) 0 0 at h20
  change (matrix F ⟨1,0,0⟩ * g.val) 0 2 = (g.val * matrix F ⟨1,0,0⟩) 0 2 at h12
  change (matrix F ⟨0,0,1⟩ * g.val) 0 1 = (g.val * matrix F ⟨0,0,1⟩) 0 1 at h21
  change (matrix F ⟨1,0,0⟩ * g.val) 0 1 = (g.val * matrix F ⟨1,0,0⟩) 0 1 at h11
  change (matrix F ⟨0,0,1⟩ * g.val) 0 2 = (g.val * matrix F ⟨0,0,1⟩) 0 2 at h22
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h12 h21 h11 h22
  have h11' : g.val 1 1 = g.val 0 0 := by linear_combination h11
  have h22' : g.val 2 2 = g.val 0 0 := by linear_combination h22
  have hmat : g.val = !![g.val 0 0,g.val 0 1,g.val 0 2;0,g.val 0 0,0;0,0,g.val 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10,h20,h12,h21,h11',h22']
  have hn : g.val 0 0 ≠ 0 := by
    intro hz
    have hd := g.property
    rw [hmat, Matrix.det_fin_three, hz] at hd
    simp at hd
  let u := specialLinear F ⟨g.val 0 1 / g.val 0 0,0,g.val 0 2 / g.val 0 0⟩
  have he : g.val = g.val 0 0 • u.val := by
    rw [hmat]
    change _ = g.val 0 0 • matrix F _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix, hn, mul_div_cancel₀]
  rw [projective_eq_of_scalar F g u (g.val 0 0) he]
  exact Subgroup.mem_map_of_mem (projection F)
    ((mem_rootPlaneSL_point F u).mpr ⟨_,_,rfl⟩)

omit [Finite F] [CharP F 2] in
private theorem line_centralizer_projective (g : SL(3,F))
    (hc : ∀ b c : F, specialLinear F ⟨0,b,c⟩ * g = g * specialLinear F ⟨0,b,c⟩) :
    projection F g ∈ rootPlane F false := by
  have h01 := congrArg (fun h : SL(3,F) => h.val 0 2) (hc 1 0)
  have h20 := congrArg (fun h : SL(3,F) => h.val 0 0) (hc 0 1)
  have h10 := congrArg (fun h : SL(3,F) => h.val 1 2) (hc 0 1)
  have h21 := congrArg (fun h : SL(3,F) => h.val 0 1) (hc 0 1)
  have h11 := congrArg (fun h : SL(3,F) => h.val 1 2) (hc 1 0)
  have h22 := congrArg (fun h : SL(3,F) => h.val 0 2) (hc 0 1)
  change (matrix F ⟨0,1,0⟩ * g.val) 0 2 = (g.val * matrix F ⟨0,1,0⟩) 0 2 at h01
  change (matrix F ⟨0,0,1⟩ * g.val) 0 0 = (g.val * matrix F ⟨0,0,1⟩) 0 0 at h20
  change (matrix F ⟨0,0,1⟩ * g.val) 1 2 = (g.val * matrix F ⟨0,0,1⟩) 1 2 at h10
  change (matrix F ⟨0,0,1⟩ * g.val) 0 1 = (g.val * matrix F ⟨0,0,1⟩) 0 1 at h21
  change (matrix F ⟨0,1,0⟩ * g.val) 1 2 = (g.val * matrix F ⟨0,1,0⟩) 1 2 at h11
  change (matrix F ⟨0,0,1⟩ * g.val) 0 2 = (g.val * matrix F ⟨0,0,1⟩) 0 2 at h22
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h01 h20 h10 h21 h11 h22
  have h22' : g.val 2 2 = g.val 0 0 := by linear_combination h22
  have h11' : g.val 1 1 = g.val 0 0 := by linear_combination h22' - h11
  have hmat : g.val = !![g.val 0 0,0,g.val 0 2;0,g.val 0 0,g.val 1 2;0,0,g.val 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01,h20,h10,h21,h11',h22']
  have hn : g.val 0 0 ≠ 0 := by
    intro hz
    have hd := g.property
    rw [hmat, Matrix.det_fin_three, hz] at hd
    simp at hd
  let u := specialLinear F ⟨0,g.val 1 2 / g.val 0 0,g.val 0 2 / g.val 0 0⟩
  have he : g.val = g.val 0 0 • u.val := by
    rw [hmat]
    change _ = g.val 0 0 • matrix F _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix, hn, mul_div_cancel₀]
  rw [projective_eq_of_scalar F g u (g.val 0 0) he]
  exact Subgroup.mem_map_of_mem (projection F)
    ((mem_rootPlaneSL_line F u).mpr ⟨_,_,rfl⟩)

omit [Finite F] in
/-- The root planes are self-centralizing in the actual PSL₃ carrier. -/
theorem centralizer_rootPlane_le (point : Bool) :
    Subgroup.centralizer (rootPlane F point : Set PSL(3,F)) ≤ rootPlane F point := by
  intro x hx
  obtain ⟨g,rfl⟩ := projection_surjective F x
  have hc (u : SL(3,F)) (hu : u ∈ rootPlaneSL F point) : u*g = g*u := by
    have hu' := rootPlaneSL_le_unipotent F point hu
    have hp := (Subgroup.mem_centralizer_iff.mp hx) (projection F u)
      (Subgroup.mem_map_of_mem (projection F) hu)
    have he : projection F (g*u*g⁻¹) = projection F u := by
      rw [map_mul, map_mul, map_inv, ← hp, mul_assoc, mul_inv_cancel, mul_one]
    have hl := conjugate_eq_of_projective_eq F g u u hu' hu' he
    have h := congrArg (fun a : SL(3,F) => a*g) hl
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm
  cases point
  · apply line_centralizer_projective F g
    intro b c
    exact hc _ ((mem_rootPlaneSL_line F _).mpr ⟨b,c,rfl⟩)
  · apply point_centralizer_projective F g
    intro a c
    exact hc _ ((mem_rootPlaneSL_point F _).mpr ⟨a,c,rfl⟩)

/-- Both full projective parabolics have characteristic two. -/
theorem parabolic_characteristicTwo (point : Bool) : HasCharacteristicTwo (parabolic F point) := by
  apply centralizer_pCore_le_of_normalized 2 (rootPlane F point) (parabolic F point)
    (rootPlane_two F point)
  · rw [rootPlane, parabolic_eq_map]
    exact Subgroup.map_mono (rootPlaneSL_le_parabolic F point)
  · rw [normalizer_rootPlane]
  · exact centralizer_rootPlane_le F point

end CFSG.Quasithin.MainConverse.LinearThreeGeometry
