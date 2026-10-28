module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation.Coordinates

/-!
# Matrix shape of a projective local normalizer

An involution whose projective image lies in a local factor lies in its
literal SL₃ preimage: a possible scalar multiplier has square one, hence is
one in characteristic two. Applying this to the two Levi transvections
shows that a linear actor preserving the point local fixes the first
coordinate line, and one preserving the line local fixes the last covector
line. Thus the GL₃ representative has the required parabolic zero entries.

Source: the local-normalizer calculation used in Aschbacher–Smith F.1.12,
printed p.264 (PDF p.275).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
variable (F : Type*) [Field F] [CharP F 2]
omit [CharP F 2] in
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

private theorem square_one_scalar (r : F) (h : r * r = 1) : r = 1 := by
  rcases sq_eq_one_iff.mp (show r ^ 2 = 1 by simpa only [pow_two] using h) with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

theorem involution_mem_localSL (point : Bool) (x : SL(3,F)) (hx : x ^ 2 = 1)
    (h : projection F x ∈ localFactor F point) : x ∈ localSL F point := by
  obtain ⟨y, hy⟩ := (localProjectEquiv F point).surjective ⟨projection F x, h⟩
  have he : projection F x = projection F y.val := by
    simpa only [localProjectEquiv_val] using (congrArg Subtype.val hy).symm
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F x y.val he
  have hr1 : r = 1 := by
    apply square_one_scalar F r
    cases point
    · have hy := (mem_lineLocalSL_iff F y.val).mp y.property
      have ht := congrArg (fun z : SL(3,F) => z.val 2 2) hx
      simp only [pow_two, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] at ht
      rw [hr] at ht
      simpa [Matrix.mul_apply, Fin.sum_univ_three, hy.1,hy.2.1,hy.2.2] using ht
    · have hy := (mem_pointLocalSL_iff F y.val).mp y.property
      have ht := congrArg (fun z : SL(3,F) => z.val 0 0) hx
      simp only [pow_two, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] at ht
      rw [hr] at ht
      simpa [Matrix.mul_apply, Fin.sum_univ_three, hy.1,hy.2.1,hy.2.2] using ht
  have he : x = y.val := Subtype.ext (by simpa only [hr1, one_smul] using hr)
  rw [he]
  exact y.property

private theorem transvection_sq (i j : Fin 3) (hij : i ≠ j) :
    (SpecialLinearGroup.transvection hij (1 : F)) ^ 2 = 1 := by
  rw [pow_two, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

omit [CharP F 2] in
private theorem linearConjSL_val (m : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F m x).val = m.val * x.val * m.inv :=
  congrArg Units.val (linearConjSL_toGL F m x)

private theorem inverse_preserves {G : Type*} [Group G] (H : Subgroup G) (a : MulAut G)
    (h : H.map a.toMonoidHom = H) : H.map a⁻¹.toMonoidHom = H := by
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  have he : a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
    ext x
    exact a.symm_apply_apply x
  rw [he, Subgroup.map_id]

private theorem conjugate_transvection_mem (point : Bool) (g : GL (Fin 3) F)
    (h : (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point)
    (i j : Fin 3) (hij : i ≠ j)
    (hu : SpecialLinearGroup.transvection hij (1 : F) ∈ localSL F point) :
    linearConjSL F g (SpecialLinearGroup.transvection hij (1 : F)) ∈ localSL F point := by
  apply involution_mem_localSL F point
  · rw [← map_pow, transvection_sq, map_one]
  · apply h.le
    rw [show projection F (linearConjSL F g (SpecialLinearGroup.transvection hij (1 : F))) =
        linearConj F g (projection F (SpecialLinearGroup.transvection hij (1 : F))) from
      (linearConj_mk F g _).symm]
    refine Subgroup.mem_map_of_mem (linearConj F g).toMonoidHom ?_
    have hm := (localProjectEquiv F point ⟨_, hu⟩).property
    simpa only [localProjectEquiv_val] using hm

/-- The two matrix shapes forced by preserving the actual projective local. -/
def ParabolicShape (point : Bool) (g : GL (Fin 3) F) : Prop :=
  if point then g.val 1 0 = 0 ∧ g.val 2 0 = 0
  else g.val 2 0 = 0 ∧ g.val 2 1 = 0

theorem linear_preserves_shape (point : Bool) (g : GL (Fin 3) F)
    (h : (localFactor F point).map (linearConj F g).toMonoidHom = localFactor F point) :
    ParabolicShape F point g := by
  cases point
  · have hrow (i j : Fin 3) (hij : i ≠ j)
        (hu : SpecialLinearGroup.transvection hij (1 : F) ∈ localSL F false) (k : Fin 3) :
        (g.val * (SpecialLinearGroup.transvection hij (1 : F)).val) 2 k = g.val 2 k := by
      let v := linearConjSL F g (SpecialLinearGroup.transvection hij (1 : F))
      have hv := (mem_lineLocalSL_iff F v).mp
        (conjugate_transvection_mem F false g h i j hij hu)
      have he : g.val * (SpecialLinearGroup.transvection hij (1 : F)).val = v.val * g.val := by
        dsimp only [v]
        rw [linearConjSL_val, Matrix.mul_assoc, g.inv_val, mul_one]
      rw [he]
      simp [Matrix.mul_apply, Fin.sum_univ_three, hv.1,hv.2.1,hv.2.2]
    have h01 := hrow 0 1 (by decide) (by
      apply (mem_lineLocalSL_iff F _).mpr
      simp [SpecialLinearGroup.transvection_coe]) 1
    have h10 := hrow 1 0 (by decide) (by
      apply (mem_lineLocalSL_iff F _).mpr
      simp [SpecialLinearGroup.transvection_coe]) 0
    simpa [ParabolicShape, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three] using And.intro h01 h10
  · have hi : (localFactor F true).map (linearConj F g⁻¹).toMonoidHom = localFactor F true := by
      rw [map_inv]
      exact inverse_preserves _ _ h
    have hcol (i j : Fin 3) (hij : i ≠ j)
        (hu : SpecialLinearGroup.transvection hij (1 : F) ∈ localSL F true) (k : Fin 3) :
        ((SpecialLinearGroup.transvection hij (1 : F)).val * g.val) k 0 = g.val k 0 := by
      let v := linearConjSL F g⁻¹ (SpecialLinearGroup.transvection hij (1 : F))
      have hv := (mem_pointLocalSL_iff F v).mp
        (conjugate_transvection_mem F true g⁻¹ hi i j hij hu)
      have he : (SpecialLinearGroup.transvection hij (1 : F)).val * g.val = g.val * v.val := by
        dsimp only [v]
        rw [linearConjSL_val]
        change _ = g.val * (g.inv * (SpecialLinearGroup.transvection hij (1 : F)).val * g.val)
        simp only [← Matrix.mul_assoc, g.val_inv, one_mul]
      rw [he]
      simp [Matrix.mul_apply, Fin.sum_univ_three, hv.1,hv.2.1,hv.2.2]
    have h12 := hcol 1 2 (by decide) (by
      apply (mem_pointLocalSL_iff F _).mpr
      simp [SpecialLinearGroup.transvection_coe]) 1
    have h21 := hcol 2 1 (by decide) (by
      apply (mem_pointLocalSL_iff F _).mpr
      simp [SpecialLinearGroup.transvection_coe]) 2
    simpa [ParabolicShape, SpecialLinearGroup.transvection_coe,
      Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three] using And.intro h21 h12

end Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
