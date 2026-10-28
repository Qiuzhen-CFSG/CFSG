module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.Quasithin

/-!
# Root-plane normalizers in PSL₃ over a field of characteristic two

The two coordinate root planes have the full point and line parabolics as
normalizers in SL₃. The forward inclusions follow from their common fixed
vector or covector spaces; matrix multiplication gives the reverse inclusions.
Trace one removes the scalar ambiguity on passing to PSL₃. The same lifting
lemma works for every subgroup of the upper-unitriangular group, and is also
used in the coverage of arbitrary two-locals.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4 (repeated on p.482),
and the root-plane geometry of §5.3.5–7, printed p.660.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.RootPlaneGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The two root planes, with `true` denoting the point side. -/
def rootPlaneSL (point : Bool) : Subgroup SL(3,F) :=
  (if point then V₁ F else V₂ F).map (specialLinear F)

def parabolicSL (point : Bool) : Subgroup SL(3,F) :=
  if point then pointParabolicSL F else lineParabolicSL F

def rootPlane (point : Bool) : Subgroup PSL(3,F) :=
  (rootPlaneSL F point).map (projection F)

def parabolic (point : Bool) : Subgroup PSL(3,F) :=
  if point then pointParabolic F else lineParabolic F

omit [Finite F] in
theorem parabolic_eq_map (point : Bool) :
    parabolic F point = (parabolicSL F point).map (projection F) := by
  cases point <;> rfl

omit [Finite F] in
theorem mem_rootPlaneSL_point (g : SL(3,F)) :
    g ∈ rootPlaneSL F true ↔ ∃ a c : F, specialLinear F ⟨a,0,c⟩ = g := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.x,u.c,congrArg (specialLinear F)
      (U.ext rfl ((mem_V₁ F u).mp hu).symm rfl)⟩
  · rintro ⟨a,c,rfl⟩
    exact ⟨⟨a,0,c⟩,(mem_V₁ F _).mpr rfl,rfl⟩

omit [Finite F] in
theorem mem_rootPlaneSL_line (g : SL(3,F)) :
    g ∈ rootPlaneSL F false ↔ ∃ b c : F, specialLinear F ⟨0,b,c⟩ = g := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.y,u.c,congrArg (specialLinear F)
      (U.ext ((mem_V₂ F u).mp hu).symm rfl rfl)⟩
  · rintro ⟨b,c,rfl⟩
    exact ⟨⟨0,b,c⟩,(mem_V₂ F _).mpr rfl,rfl⟩

omit [Finite F] in
theorem rootPlaneSL_le_unipotent (point : Bool) :
    rootPlaneSL F point ≤ unipotentSL F := by
  rw [← specialLinear_range]
  exact Subgroup.map_le_range _ _

theorem rootPlaneSL_le_parabolic (point : Bool) :
    rootPlaneSL F point ≤ parabolicSL F point := by
  have h := (rootPlaneSL_le_unipotent F point).trans (unipotentSL_le_borelSL F)
  cases point
  · exact h.trans inf_le_right
  · exact h.trans inf_le_left

private theorem conjugate_point (g : SL(3,F)) (hg : g ∈ pointParabolicSL F) (a c : F) :
    g * specialLinear F ⟨a,0,c⟩ * g⁻¹ =
      specialLinear F ⟨g.val 0 0 * (a * g⁻¹.val 1 1 + c * g⁻¹.val 2 1), 0,
        g.val 0 0 * (a * g⁻¹.val 1 2 + c * g⁻¹.val 2 2)⟩ := by
  obtain ⟨g10,g20⟩ := (mem_pointParabolicSL_iff F g).mp hg
  obtain ⟨i10,i20⟩ := (mem_pointParabolicSL_iff F g⁻¹).mp ((pointParabolicSL F).inv_mem hg)
  have hi : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  have hm : matrix F ⟨a,0,c⟩ = 1 + !![0,a,c;0,0,0;0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  apply Subtype.ext
  change g.val * matrix F ⟨a,0,c⟩ * g⁻¹.val = matrix F _
  rw [hm, mul_add, mul_one, add_mul, hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Matrix.SpecialLinearGroup.coe_inv, matrix, Matrix.mul_apply, Fin.sum_univ_three,
      g10,g20,i10,i20] <;> ring

private theorem conjugate_line (g : SL(3,F)) (hg : g ∈ lineParabolicSL F) (b c : F) :
    g * specialLinear F ⟨0,b,c⟩ * g⁻¹ =
      specialLinear F ⟨0, (g.val 1 0 * c + g.val 1 1 * b) * g⁻¹.val 2 2,
        (g.val 0 0 * c + g.val 0 1 * b) * g⁻¹.val 2 2⟩ := by
  obtain ⟨g20,g21⟩ := (mem_lineParabolicSL_iff F g).mp hg
  obtain ⟨i20,i21⟩ := (mem_lineParabolicSL_iff F g⁻¹).mp ((lineParabolicSL F).inv_mem hg)
  have hi : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  have hm : matrix F ⟨0,b,c⟩ = 1 + !![0,0,c;0,0,b;0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  apply Subtype.ext
  change g.val * matrix F ⟨0,b,c⟩ * g⁻¹.val = matrix F _
  rw [hm, mul_add, mul_one, add_mul, hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-Matrix.SpecialLinearGroup.coe_inv, matrix, Matrix.mul_apply, Fin.sum_univ_three,
      g20,g21,i20,i21]

theorem parabolicSL_le_normalizer_rootPlaneSL (point : Bool) :
    parabolicSL F point ≤ Subgroup.normalizer (rootPlaneSL F point) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg u hu
  cases point
  · obtain ⟨b,c,rfl⟩ := (mem_rootPlaneSL_line F u).mp hu
    rw [conjugate_line F g hg b c]
    exact (mem_rootPlaneSL_line F _).mpr ⟨_,_,rfl⟩
  · obtain ⟨a,c,rfl⟩ := (mem_rootPlaneSL_point F u).mp hu
    rw [conjugate_point F g hg a c]
    exact (mem_rootPlaneSL_point F _).mpr ⟨_,_,rfl⟩

theorem normalizer_rootPlaneSL (point : Bool) :
    Subgroup.normalizer (rootPlaneSL F point) = parabolicSL F point := by
  apply le_antisymm _ (parabolicSL_le_normalizer_rootPlaneSL F point)
  intro g hg
  cases point
  · have hrow (b c : F) (j : Fin 3) :
        (g * specialLinear F ⟨0,b,c⟩).val 2 j = g.val 2 j := by
      let v := g * specialLinear F ⟨0,b,c⟩ * g⁻¹
      have hv : v ∈ rootPlaneSL F false :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp
          ((mem_rootPlaneSL_line F _).mpr ⟨b,c,rfl⟩)
      obtain ⟨d,e,he⟩ := (mem_rootPlaneSL_line F v).mp hv
      have hmul : g * specialLinear F ⟨0,b,c⟩ = v * g := by dsimp [v]; group
      rw [hmul, ← he]
      change (matrix F ⟨0,d,e⟩ * g.val) 2 j = g.val 2 j
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three]
    have h20 := hrow 0 1 2
    have h21 := hrow 1 0 2
    change (g.val * matrix F ⟨0,0,1⟩) 2 2 = g.val 2 2 at h20
    change (g.val * matrix F ⟨0,1,0⟩) 2 2 = g.val 2 2 at h21
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h20 h21
    exact (mem_lineParabolicSL_iff F g).mpr ⟨h20,h21⟩
  · have hcol (a c : F) (i : Fin 3) :
        (specialLinear F ⟨a,0,c⟩ * g).val i 0 = g.val i 0 := by
      let v := g⁻¹ * specialLinear F ⟨a,0,c⟩ * g
      have hv : v ∈ rootPlaneSL F true :=
        (Subgroup.mem_normalizer_iff''.mp hg _).mp
          ((mem_rootPlaneSL_point F _).mpr ⟨a,c,rfl⟩)
      obtain ⟨d,e,he⟩ := (mem_rootPlaneSL_point F v).mp hv
      have hmul : specialLinear F ⟨a,0,c⟩ * g = g * v := by dsimp [v]; group
      rw [hmul, ← he]
      change (g.val * matrix F ⟨d,0,e⟩) i 0 = g.val i 0
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three]
    have h10 := hcol 1 0 0
    have h20 := hcol 0 1 0
    change (matrix F ⟨1,0,0⟩ * g.val) 0 0 = g.val 0 0 at h10
    change (matrix F ⟨0,0,1⟩ * g.val) 0 0 = g.val 0 0 at h20
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20
    exact (mem_pointParabolicSL_iff F g).mpr ⟨h10,h20⟩



variable [CharP F 2]

omit [Finite F] in
private theorem trace_unipotent (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
    Matrix.trace u.val = 1 := by
  rw [(mem_unipotentSL_iff F u).mp hu]
  simp [Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

omit [Finite F] in
/-- Trace removes the scalar ambiguity between two unipotent representatives. -/
theorem conjugate_eq_of_projective_eq (g u v : SL(3,F))
    (hu : u ∈ unipotentSL F) (hv : v ∈ unipotentSL F)
    (h : projection F (g*u*g⁻¹) = projection F v) : g*u*g⁻¹ = v := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have he : (g*u*g⁻¹).val = r • v.val := by
    calc
      (g*u*g⁻¹).val = (v * (v⁻¹ * (g*u*g⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = v.val * Matrix.scalar (Fin 3) r := by rw [Matrix.SpecialLinearGroup.coe_mul, ← hr]
      _ = r • v.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have ht : Matrix.trace (g*u*g⁻¹).val = 1 := by
    change Matrix.trace (g.val*u.val*g⁻¹.val) = 1
    rw [Matrix.trace_mul_cycle]
    have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [hi, one_mul]
    exact trace_unipotent F u hu
  rw [he, Matrix.trace_smul, trace_unipotent F v hv, smul_eq_mul, mul_one] at ht
  exact Subtype.ext (by simpa [ht] using he)

/-- Normalizers of any subgroup of UT₃ lift through the scalar quotient. -/
theorem normalizer_map_comap (Q : Subgroup SL(3,F)) (hQ : Q ≤ unipotentSL F) :
    (Subgroup.normalizer (Q.map (projection F))).comap (projection F) =
      Subgroup.normalizer Q := by
  apply le_antisymm
  · intro g hg
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have hproj := (Subgroup.mem_normalizer_iff.mp hg (projection F u)).mp
      (Subgroup.mem_map_of_mem (projection F) hu)
    obtain ⟨v,hv,he⟩ := hproj
    have h : g*u*g⁻¹ = v := conjugate_eq_of_projective_eq F g u v (hQ hu) (hQ hv)
      (by simpa only [map_mul, map_inv] using he.symm)
    exact h ▸ hv
  · intro g hg
    exact (Q.le_normalizer_map (projection F)) (Subgroup.mem_map_of_mem (projection F) hg)

theorem normalizer_rootPlane (point : Bool) :
    Subgroup.normalizer (rootPlane F point) = parabolic F point := by
  apply (Subgroup.comap_injective (projection_surjective F))
  rw [rootPlane, normalizer_map_comap F _ (rootPlaneSL_le_unipotent F point),
    normalizer_rootPlaneSL]
  cases point
  · exact (lineParabolic_comap F).symm
  · exact (pointParabolic_comap F).symm

omit [Finite F] in
theorem rootPlane_two (point : Bool) : IsPGroup 2 (rootPlane F point) := by
  apply IsPGroup.map
  cases point
  · exact (IsElementaryAbelian.isPGroup 2 (V₂ F)).map (specialLinear F)
  · exact (IsElementaryAbelian.isPGroup 2 (V₁ F)).map (specialLinear F)

omit [Finite F] [CharP F 2] in
theorem rootPlane_ne_bot (point : Bool) : rootPlane F point ≠ ⊥ := by
  intro h
  have hm : projection F (specialLinear F ⟨0,0,1⟩) ∈ rootPlane F point := by
    apply Subgroup.mem_map_of_mem
    cases point
    · exact (mem_rootPlaneSL_line F _).mpr ⟨0,1,rfl⟩
    · exact (mem_rootPlaneSL_point F _).mpr ⟨0,1,rfl⟩
  have he : projective F ⟨0,0,1⟩ = projective F 1 := by
    change projection F (specialLinear F ⟨0,0,1⟩) = _
    simpa only [h, Subgroup.mem_bot, map_one] using hm
  have he' := congrArg U.c (projective_injective F he)
  exact one_ne_zero he'

theorem parabolic_twoLocal (point : Bool) : IsTwoLocal (parabolic F point) :=
  ⟨rootPlane F point, rootPlane_ne_bot F point, rootPlane_two F point,
    (normalizer_rootPlane F point).symm⟩

end Matrix.PSL3.RootPlaneGeometry
