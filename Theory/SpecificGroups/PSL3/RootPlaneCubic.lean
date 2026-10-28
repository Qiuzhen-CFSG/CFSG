module
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# Scalar cubes of root-plane stabilizers in PGL₃

A general linear representative of a projective root-plane stabilizer preserves
its coordinate line or plane. Trace one removes the scalar ambiguity on lifting
root elements to SL₃. The resulting zero entries show that a scalar cube has a
cube root in the coefficient field: its distinguished diagonal entry.

This rules out the nonsplit cubic case in the root-plane normal-form argument.
Source: Aschbacher--Smith B.4.14, printed p.98, and the natural parabolic
geometry in GLS3, §2.7.
-/

public noncomputable section
open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.RootPlaneCubic
variable (F : Type*) [Field F]

private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem linearConjSL_val (g : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F g x).val = g.val * x.val * g.inv :=
  congrArg Units.val (linearConjSL_toGL F g x)

variable [CharP F 2]

private theorem trace_root (u : SL(3,F)) (b : Bool) (hu : u ∈ rootPlaneSL F b) :
    Matrix.trace u.val = 1 := by
  rw [(mem_unipotentSL_iff F u).mp (rootPlaneSL_le_unipotent F b hu)]
  simp [Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

/-- Projective root-plane membership lifts without a scalar ambiguity. -/
theorem linearConjSL_mem_rootPlane (g : GL (Fin 3) F) (b : Bool)
    (u : SL(3,F)) (hu : u ∈ rootPlaneSL F b)
    (h : linearConj F g (projection F u) ∈ rootPlane F b) :
    linearConjSL F g u ∈ rootPlaneSL F b := by
  obtain ⟨v,hv,hproj⟩ := h
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F (linearConjSL F g u) v hproj.symm
  have ht : Matrix.trace (linearConjSL F g u).val = 1 := by
    rw [linearConjSL_val, Matrix.trace_mul_cycle, g.inv_val, one_mul]
    exact trace_root F u b hu
  rw [hr, Matrix.trace_smul, trace_root F v b hv, smul_eq_mul, mul_one] at ht
  have he : linearConjSL F g u = v := Subtype.ext (by simpa [ht] using hr)
  rwa [he]

/-- A projective root-plane stabilizer preserves the corresponding coordinate
line or coordinate plane in the natural three-space. -/
theorem parabolic_entries (g : GL (Fin 3) F) (b : Bool)
    (h : (rootPlane F b).map (linearConj F g).toMonoidHom = rootPlane F b) :
    if b then g.val 1 0 = 0 ∧ g.val 2 0 = 0
    else g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  have hf (u : SL(3,F)) (hu : u ∈ rootPlaneSL F b) :
      linearConjSL F g u ∈ rootPlaneSL F b :=
    linearConjSL_mem_rootPlane F g b u hu
      (h.le (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem (projection F) hu)))
  have hi : (rootPlane F b).map (linearConj F g⁻¹).toMonoidHom = rootPlane F b := by
    rw [map_inv]
    conv_lhs => rw [←h]
    rw [Subgroup.map_map]
    have he : (linearConj F g)⁻¹.toMonoidHom.comp (linearConj F g).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      exact (linearConj F g).symm_apply_apply x
    rw [he,Subgroup.map_id]
  have hb (u : SL(3,F)) (hu : u ∈ rootPlaneSL F b) :
      linearConjSL F g⁻¹ u ∈ rootPlaneSL F b :=
    linearConjSL_mem_rootPlane F g⁻¹ b u hu
      (hi.le (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem (projection F) hu)))
  cases b
  · have hrow (a c : F) (j : Fin 3) :
        (g.val * (specialLinear F ⟨0,a,c⟩).val) 2 j = g.val 2 j := by
      let v := linearConjSL F g (specialLinear F ⟨0,a,c⟩)
      obtain ⟨d,e,he⟩ := (mem_rootPlaneSL_line F v).mp
        (hf _ ((mem_rootPlaneSL_line F _).mpr ⟨a,c,rfl⟩))
      have hm : g.val * (specialLinear F ⟨0,a,c⟩).val = v.val * g.val := by
        dsimp only [v]
        rw [linearConjSL_val, Matrix.mul_assoc, g.inv_val, mul_one]
      rw [hm,←he]
      change (matrix F ⟨0,d,e⟩ * g.val) 2 j = g.val 2 j
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three]
    have h20 := hrow 0 1 2
    have h21 := hrow 1 0 2
    change (g.val * matrix F ⟨0,0,1⟩) 2 2 = g.val 2 2 at h20
    change (g.val * matrix F ⟨0,1,0⟩) 2 2 = g.val 2 2 at h21
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h20 h21
    exact ⟨h20,h21⟩
  · have hcol (a c : F) (i : Fin 3) :
        ((specialLinear F ⟨a,0,c⟩).val * g.val) i 0 = g.val i 0 := by
      let v := linearConjSL F g⁻¹ (specialLinear F ⟨a,0,c⟩)
      obtain ⟨d,e,he⟩ := (mem_rootPlaneSL_point F v).mp
        (hb _ ((mem_rootPlaneSL_point F _).mpr ⟨a,c,rfl⟩))
      have hm : (specialLinear F ⟨a,0,c⟩).val * g.val = g.val * v.val := by
        dsimp only [v]
        rw [linearConjSL_val]
        change _ = g.val * (g.inv * (specialLinear F ⟨a,0,c⟩).val * g.val)
        simp only [←Matrix.mul_assoc,g.val_inv,one_mul]
      rw [hm,←he]
      change (g.val * matrix F ⟨d,0,e⟩) i 0 = g.val i 0
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three]
    have h10 := hcol 1 0 0
    have h20 := hcol 0 1 0
    change (matrix F ⟨1,0,0⟩ * g.val) 0 0 = g.val 0 0 at h10
    change (matrix F ⟨0,0,1⟩ * g.val) 0 0 = g.val 0 0 at h20
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20
    exact ⟨h10,h20⟩

/-- A scalar cube of a root-plane-preserving lift has a cube root in the
coefficient field. The invariant coordinate line or plane excludes the
irreducible cubic case. -/
theorem scalar_cube_has_root (g : GL (Fin 3) F) (b : Bool)
    (h : (rootPlane F b).map (linearConj F g).toMonoidHom = rootPlane F b)
    (z : Fˣ) (hc : g ^ 3 = GeneralLinearGroup.scalar (Fin 3) z) :
    ∃ a : F, a ^ 3 = (z : F) := by
  have he := parabolic_entries F g b h
  cases b
  · obtain ⟨h20,h21⟩ := he
    refine ⟨g.val 2 2, ?_⟩
    have hh := congrArg (fun x : GL (Fin 3) F => x.val 2 2) hc
    simpa [pow_succ,Matrix.mul_apply,Fin.sum_univ_three,h20,h21] using hh
  · obtain ⟨h10,h20⟩ := he
    refine ⟨g.val 0 0, ?_⟩
    have hh := congrArg (fun x : GL (Fin 3) F => x.val 0 0) hc
    simpa [pow_succ,Matrix.mul_apply,Fin.sum_univ_three,h10,h20] using hh

/-- A projective cubic preserving a root plane has a lift with split scalar
cube, with the same matrix representative and literal projective action. -/
theorem projective_cube_has_root (actor : ProjGenLinGroup (Fin 3) F)
    (b : Bool) (hc : actor ^ 3 = 1)
    (h : (rootPlane F b).map (ExtensionBorel.pglEquivInnerDiagonal F actor).val.toMonoidHom =
      rootPlane F b) :
    ∃ (g : GL (Fin 3) F) (z : Fˣ) (a : F),
      ProjGenLinGroup.mk g = actor ∧
      g ^ 3 = GeneralLinearGroup.scalar (Fin 3) z ∧ a ^ 3 = (z : F) := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective actor
  have hg : g^3 ∈ center (GL (Fin 3) F) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    rwa [map_pow]
  obtain ⟨z,hz⟩ := GeneralLinearGroup.center_eq_range_scalar (n := Fin 3) (R := F) ▸ hg
  obtain ⟨a,ha⟩ := scalar_cube_has_root F g b h z hz.symm
  exact ⟨g,z,a,rfl,hz.symm,ha⟩

end Matrix.PSL3.RootPlaneCubic
