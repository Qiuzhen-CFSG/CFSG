module

public import Theory.SpecificGroups.PSL4Three.SectionReduction
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Invariant subspaces for the proper-subgroup problem in PSL₄(3)

The parabolic attached to a subspace is the setwise stabilizer in the actual
special linear matrix group, followed by the central quotient. Reducibility
means containment in one of these parabolics for a nonzero proper subspace.
It does not assert that all proper subgroups are reducible.

This supplies the geometric division for the intrinsic subgroup analysis
needed in Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, and condition K,
printed p.482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups

open scoped Pointwise

public abbrev SL := SpecialLinearGroup (Fin 4) (ZMod 3)
public abbrev Vec := Fin 4 → ZMod 3

/-- The actual central quotient map. -/
@[expose] public def project : SL →* PSL := QuotientGroup.mk' (Subgroup.center SL)

/-- Setwise, rather than pointwise, stabilization of the subspace. -/
@[expose] public def parabolic (W : Submodule (ZMod 3) Vec) : Subgroup SL :=
  MulAction.stabilizer SL (W : Set Vec)

/-- The projective image of a subspace stabilizer. -/
@[expose] public def projectiveParabolic (W : Submodule (ZMod 3) Vec) : Subgroup PSL :=
  (parabolic W).map project

private theorem center_le_parabolic (W : Submodule (ZMod 3) Vec) :
    Subgroup.center SL ≤ parabolic W := by
  intro g hg
  obtain ⟨a, _, ha⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  apply (MulAction.mem_stabilizer_set' (Set.toFinite (W : Set Vec))).mpr
  intro v hv
  change ((g : Matrix (Fin 4) (Fin 4) (ZMod 3)) *ᵥ v) ∈ W
  rw [← ha]
  have he : Matrix.scalar (Fin 4) a *ᵥ v = a • v := by
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [he]
  exact W.smul_mem a hv

/-- Passing to the projective image and pulling back restores the full
stabilizer: all central scalars preserve every subspace. -/
public theorem comap_projectiveParabolic (W : Submodule (ZMod 3) Vec) :
    (projectiveParabolic W).comap project = parabolic W := by
  apply Subgroup.comap_map_eq_self
  simpa only [project, QuotientGroup.ker_mk'] using center_le_parabolic W

/-- Projective containment is equivalent to invariance under all matrix lifts. -/
public theorem le_projectiveParabolic_iff (U : Subgroup PSL)
    (W : Submodule (ZMod 3) Vec) :
    U ≤ projectiveParabolic W ↔ U.comap project ≤ parabolic W := by
  constructor
  · intro h
    simpa only [comap_projectiveParabolic] using Subgroup.comap_mono (f := project) h
  · intro h
    have hm := Subgroup.map_mono (f := project) h
    have hs : Function.Surjective project := QuotientGroup.mk'_surjective _
    simpa only [projectiveParabolic, Subgroup.map_comap_eq_self_of_surjective hs] using hm

/-- A proper nonzero invariant subspace in the natural matrix representation. -/
@[expose] public def Reducible (U : Subgroup PSL) : Prop :=
  ∃ W : Submodule (ZMod 3) Vec, W ≠ ⊥ ∧ W ≠ ⊤ ∧ U ≤ projectiveParabolic W

/-- The first coordinate vector. -/
@[expose] public def firstVector : Vec := Pi.single 0 1

/-- The first coordinate line. -/
@[expose] public def firstLine : Submodule (ZMod 3) Vec where
  carrier := {v | ∀ i : Fin 3, v i.succ = 0}
  zero_mem' _ := rfl
  add_mem' := by
    intro v w hv hw i
    exact (congrArg₂ (· + ·) (hv i) (hw i)).trans (zero_add 0)
  smul_mem' := by
    intro a v hv i
    exact (congrArg (a * ·) (hv i)).trans (mul_zero a)

public theorem firstVector_mem_firstLine : firstVector ∈ firstLine := by
  simp [firstLine, firstVector]

/-- This coordinate submodule is exactly the span of the marked vector. -/
public theorem firstLine_eq_span :
    firstLine = Submodule.span (ZMod 3) {firstVector} := by
  apply le_antisymm
  · intro v hv
    have he : v = (v 0) • firstVector := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [firstVector]
      · simpa [firstVector, firstLine] using hv i
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton firstVector))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr firstVector_mem_firstLine)

end Matrix.PSL4Three.ProperOvergroups
