module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.Geometry
public import Theory.GroupTheory.SolvableLayersEmbeddingConstructions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Normal layers in the coordinate-line stabilizer of PSL₄(3)

Every lift stabilizing the coordinate line has corner entry 1 or -1.
Multiplication by the central scalar -1 therefore gives a lift fixing the
marked vector. The quotient is injective on that vector stabilizer, yielding
an actual isomorphism with the projective line stabilizer.

The lower-right three-by-three block gives a representation of the vector
stabilizer in GL₃(3). Its kernel consists of matrices with identity diagonal
blocks and one arbitrary off-diagonal row, and is abelian. The first
isomorphism theorem constructs the required faithful quotient map. Restricting
this representation also proves the result for every subgroup of a conjugate.

This proves one parabolic case needed for Aschbacher–Smith, Theorem 0.1.2(4)
and condition K, printed pp.4 and 482 of `refs/quasithin.pdf`. No exhaustive
subgroup classification is asserted here.
-/

namespace Matrix.PSL4Three.ProperOvergroups

/-- The subgroup fixing the first coordinate vector. -/
@[expose] public def pointStabilizerSL : Subgroup SL := MulAction.stabilizer SL firstVector

private theorem point_first_col (g : pointStabilizerSL) (i : Fin 4) :
    g.val i 0 = if i = 0 then 1 else 0 := by
  have h := congrFun (MulAction.mem_stabilizer_iff.mp g.property) i
  change ((g.val : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ firstVector) i = _ at h
  simpa [firstVector, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply] using h

private def pointBlock (g : pointStabilizerSL) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => g.val i.succ j.succ

private theorem pointBlock_one : pointBlock 1 = 1 := by
  ext i j
  simp [pointBlock, Matrix.one_apply]

private theorem pointBlock_mul (g h : pointStabilizerSL) :
    pointBlock (g * h) = pointBlock g * pointBlock h := by
  ext i j
  change (∑ k : Fin 4, g.val i.succ k * h.val k j.succ) =
    ∑ k : Fin 3, g.val i.succ k.succ * h.val k.succ j.succ
  rw [Fin.sum_univ_succ]
  simp [point_first_col g]

/-- The action on the three-dimensional quotient by the fixed line. -/
public def pointAction : pointStabilizerSL →* GeneralLinearGroup (Fin 3) (ZMod 3) where
  toFun g :=
    { val := pointBlock g
      inv := pointBlock g⁻¹
      val_inv := by rw [← pointBlock_mul, mul_inv_cancel, pointBlock_one]
      inv_val := by rw [← pointBlock_mul, inv_mul_cancel, pointBlock_one] }
  map_one' := Units.ext pointBlock_one
  map_mul' g h := Units.ext (pointBlock_mul g h)

private theorem pointAction_ker_commutative :
    ∀ g h : pointAction.ker, g * h = h * g := by
  intro g h
  have gb : pointBlock g.val = 1 := congrArg Units.val g.property
  have hb : pointBlock h.val = 1 := congrArg Units.val h.property
  have gentry (i j : Fin 3) : g.val.val i.succ j.succ = if i = j then 1 else 0 := by
    simpa [pointBlock, Matrix.one_apply] using congrFun (congrFun gb i) j
  have hentry (i j : Fin 3) : h.val.val i.succ j.succ = if i = j then 1 else 0 := by
    simpa [pointBlock, Matrix.one_apply] using congrFun (congrFun hb i) j
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, point_first_col]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, point_first_col, gentry, hentry,
        add_comm]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Matrix.mul_apply, point_first_col]
    · change pointBlock (g.val * h.val) i j = pointBlock (h.val * g.val) i j
      rw [pointBlock_mul, pointBlock_mul, gb, hb]

private theorem pointProject_injective :
    Function.Injective (project.comp pointStabilizerSL.subtype) := by
  apply (project.comp pointStabilizerSL.subtype).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hc : g.val ∈ Subgroup.center SL := (QuotientGroup.eq_one_iff _).mp hg
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc 0
  have hg00 : g.val 0 0 = 1 := by simpa using point_first_col g 0
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subtype.ext
  simpa [hg00] using hs.symm

private theorem line_first_col (g : parabolic firstLine) (i : Fin 3) :
    g.val i.succ 0 = 0 := by
  have hv : firstVector ∈ firstLine := by simp [firstLine, firstVector]
  have h := (MulAction.mem_stabilizer_set' (Set.toFinite (firstLine : Set Vec))).mp
    g.property hv i
  change ((g.val : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ firstVector) i.succ = 0 at h
  simpa [firstVector, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply] using h

private theorem mem_line_of_first_col (g : SL) (hg : ∀ i : Fin 3, g i.succ 0 = 0) :
    g ∈ parabolic firstLine := by
  apply (MulAction.mem_stabilizer_set' (Set.toFinite (firstLine : Set Vec))).mpr
  intro v hv i
  change ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ v) i.succ = 0
  change ∀ j : Fin 3, v j.succ = 0 at hv
  simp [mulVec, dotProduct, Fin.sum_univ_succ, hg, hv]

private theorem point_le_line : pointStabilizerSL ≤ parabolic firstLine := by
  intro g hg
  apply mem_line_of_first_col
  intro i
  simpa using point_first_col ⟨g, hg⟩ i.succ

private theorem line_corner_ne_zero (g : parabolic firstLine) : g.val 0 0 ≠ 0 := by
  have h := congrArg (fun a : SL => a 0 0) (mul_inv_cancel g.val)
  change (∑ k : Fin 4, g.val 0 k * (g.val)⁻¹ k 0) = 1 at h
  have hz (i : Fin 3) : (g.val)⁻¹ i.succ 0 = 0 := line_first_col g⁻¹ i
  simp only [Fin.sum_univ_succ, hz, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact left_ne_zero_of_mul_eq_one h

private instance : Fact (Even (Fintype.card (Fin 4))) := ⟨by decide⟩

private theorem project_neg_one : project (-1 : SL) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply SpecialLinearGroup.mem_center_iff.mpr
  exact ⟨-1, by decide, by decide⟩

private theorem line_project_lift (g : parabolic firstLine) :
    ∃ h : pointStabilizerSL, project h.val = project g.val := by
  have hsign : g.val 0 0 = 1 ∨ g.val 0 0 = -1 :=
    (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) _ (line_corner_ne_zero g)
  have fix_or_neg (s : SL) (hs0 : s 0 0 = 1) (hs : ∀ i : Fin 3, s i.succ 0 = 0) :
      s ∈ pointStabilizerSL := by
    apply MulAction.mem_stabilizer_iff.mpr
    funext i
    change ((s : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ firstVector) i = firstVector i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [firstVector, mulVec, dotProduct, Pi.single_apply, hs0, hs]
  rcases hsign with h | h
  · exact ⟨⟨g.val, fix_or_neg g.val h (line_first_col g)⟩, rfl⟩
  · let s : SL := (-1) * g.val
    have hs : s ∈ pointStabilizerSL := by
      apply fix_or_neg
      · change ((-1) * g.val) 0 0 = 1
        rw [neg_one_mul]
        change -(g.val 0 0) = 1
        rw [h, neg_neg]
      · intro i
        change ((-1) * g.val) i.succ 0 = 0
        rw [neg_one_mul]
        change -(g.val i.succ 0) = 0
        rw [line_first_col, neg_zero]
    refine ⟨⟨s, hs⟩, ?_⟩
    change project ((-1) * g.val) = project g.val
    rw [map_mul, project_neg_one, one_mul]

private theorem pointProject_range :
    (project.comp pointStabilizerSL.subtype).range = projectiveParabolic firstLine := by
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    exact ⟨g.val, point_le_line g.property, rfl⟩
  · rintro x ⟨g, hg, rfl⟩
    obtain ⟨h, hh⟩ := line_project_lift ⟨g, hg⟩
    exact ⟨h, hh⟩

/-- Normalizing a lift by its central sign identifies the vector stabilizer
with the actual projective line stabilizer. -/
public noncomputable def pointLineEquiv : pointStabilizerSL ≃* projectiveParabolic firstLine :=
  (MonoidHom.ofInjective pointProject_injective).trans
    (MulEquiv.subgroupCongr pointProject_range)

/-- Actual normal layers and a faithful quotient representation for the line parabolic. -/
public theorem line_hasSmallLayers : HasSmallLayers (projectiveParabolic firstLine) := by
  let : Group.IsSolvable pointAction.ker := Group.isSolvable_of_comm pointAction_ker_commutative
  exact Or.inl (Theory.GroupTheory.SolvableLayersEmbedding.of_solvable_ker_comp_injective
    pointAction pointLineEquiv.symm.toMonoidHom pointLineEquiv.symm.injective)

/-- The same block representation restricts to any subgroup of a conjugate. -/
public theorem line_conjugate_subgroup_hasSmallLayers (U : Subgroup PSL) (g : PSL)
    (hU : U ≤ (projectiveParabolic firstLine).map (MulAut.conj g).toMonoidHom) :
    HasSmallLayers U := by
  let e := Subgroup.equivMapOfInjective (projectiveParabolic firstLine)
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let j := (pointLineEquiv.symm.toMonoidHom.comp e.symm.toMonoidHom).comp
    (Subgroup.inclusion hU)
  have hj : Function.Injective j :=
    pointLineEquiv.symm.injective.comp (e.symm.injective.comp
      (Subgroup.inclusion_injective hU))
  let : Group.IsSolvable pointAction.ker := Group.isSolvable_of_comm pointAction_ker_commutative
  exact Or.inl (Theory.GroupTheory.SolvableLayersEmbedding.of_solvable_ker_comp_injective
    pointAction j hj)

end Matrix.PSL4Three.ProperOvergroups
