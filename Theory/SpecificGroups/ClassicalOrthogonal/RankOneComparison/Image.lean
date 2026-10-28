/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: Lean 4.33 modules, narrow imports, and CFSG quadratic-isometry carriers.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Roots
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.NilpotentLines
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic

/-!
# Exact elementary image of trace-zero SL₂ conjugation

Adapted from ATLAS `LinearGroups/Orthogonal/B1ConjugationImage.lean` and
the Siegel conjugation identity in `ElementaryNormal.lean`. Elementary
SL₂ generation puts the image inside CFSG's elementary orthogonal group.
The nilpotent-line orbit and conjugation covariance put every Siegel
transformation in the image. Thus the image is exactly the literal group
used by the B₁ carrier of GLS3 §2.7, with no perfectness or order premise.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.RankOneComparison
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration Matrix
variable {F : Type*} [Field F]

universe u
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Conjugation carries actual Siegel generators to their transported parameters. -/
private theorem siegelElement_conj (Q : QuadraticForm K V) (g : Theory.AlgebraicGroup.quadraticIsometrySubgroup Q) (u v : V)
    (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    g * siegelElement Q u v hu huv * g⁻¹ =
      siegelElement Q (g.val u) (g.val v)
        ((isometryCarrierEquiv Q g).map_app u |>.trans hu)
        ((isometry_polar Q (isometryCarrierEquiv Q g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel Q u v (g.val.symm x)) = siegel Q (g.val u) (g.val v) x
  have h := siegel_covariant Q (isometryCarrierEquiv Q g) u v (g.val.symm x)
  change g.val (siegel Q u v (g.val.symm x)) =
    siegel Q (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h


theorem toOrthogonal_mem_elementary (g : SL (F := F)) :
    toOrthogonal g ∈ elementarySubgroup (formB 1 F) := by
  apply Atlas.sl_elementary_induction (fun g => toOrthogonal g ∈ elementarySubgroup (formB 1 F)) ?_
    (fun a b ha hb => by rw [map_mul]; exact (elementarySubgroup _).mul_mem ha hb) g
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have hv : (formB 1 F).polarBilin (e 0,0) (0,-a) = 0 := by
      simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e]
    have h := standard_siegel_image (F := F) (0,-a) hv
    simp only [neg_neg] at h
    rw [← h]
    exact siegelElement_mem _ _ _ _ _
  · rw [lower_transvection_root]
    exact siegelElement_mem _ _ _ _ _
  · exact (hij rfl).elim

theorem singular_line_orbit (u : VectorB 1 F) (hu : u ≠ 0) (hqu : formB 1 F u = 0) :
    ∃ g : SL (F := F), ∃ c : F, c ≠ 0 ∧ u = c • (toOrthogonal g).val (e 0,0) := by
  have hm : (coordinates u).val ≠ 0 := by
    intro hz
    apply hu
    apply coordinates.injective
    rw [map_zero]
    apply Subtype.ext
    change (coordinates u).val = 0
    exact hz
  have hd : (coordinates u).val.det = 0 := by
    have h := (coordinates_form u).trans hqu
    exact neg_eq_zero.mp h
  have ht : (coordinates u).val.trace = 0 := (coordinates u).prop
  obtain ⟨g,c,hc,h⟩ := ClassicalOrthogonal.RankOneComparison.MatrixTwo.traceZero_singular_SL2_line (coordinates u).val hm hd ht
  refine ⟨g,c,hc,?_⟩
  apply coordinates.injective
  apply Subtype.ext
  rw [map_smul]
  change (coordinates u).val = c • (coordinates (onB g (e 0,0))).val
  rw [onB_coordinates]
  have he : (coordinates (e (F := F) (0 : Fin 1),0)).val = !![0,1;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinates,e]
  rw [he]
  have hs : (!![0,c;0,0] : Mat (F := F)) = c • !![0,1;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hs,Matrix.mul_smul,Matrix.smul_mul] at h
  exact h

theorem siegel_mem_image (u v : VectorB 1 F) (hu : formB 1 F u = 0)
    (huv : (formB 1 F).polarBilin u v = 0) :
    siegelElement (formB 1 F) u v hu huv ∈ (toOrthogonal (F := F)).range := by
  by_cases hu0 : u = 0
  · have he : siegelElement (formB 1 F) u v hu huv = 1 := by
      subst u
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB 1 F) 0 v x = x
      simp [siegel]
    rw [he]
    exact (toOrthogonal (F := F)).range.one_mem
  · obtain ⟨a,c,hc,ha⟩ := singular_line_orbit u hu0 hu
    let g := toOrthogonal a
    change u = c • g.val (e 0,0) at ha
    let w := g.val.symm (c • v)
    have hw : (formB 1 F).polarBilin (e 0,0) w = 0 := by
      have h := isometry_polar (formB 1 F) (isometryCarrierEquiv _ g) (e 0,0) w
      change (formB 1 F).polarBilin (g.val (e 0,0)) (g.val (g.val.symm (c • v))) =
        (formB 1 F).polarBilin (e 0,0) w at h
      rw [LinearEquiv.apply_symm_apply] at h
      have hh : (formB 1 F).polarBilin (g.val (e 0,0)) (c • v) = 0 := by
        rw [ha,map_smul,LinearMap.smul_apply] at huv
        simpa only [map_smul] using huv
      exact h.symm.trans hh
    have hs : siegelElement (formB 1 F) (e 0,0) w (by simp [e]) hw ∈
        (toOrthogonal (F := F)).range := by
      rw [standard_siegel_image]
      exact ⟨_,rfl⟩
    have he : g * siegelElement (formB 1 F) (e 0,0) w (by simp [e]) hw * g⁻¹ =
        siegelElement (formB 1 F) u v hu huv := by
      rw [siegelElement_conj]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formB 1 F) (g.val (e 0,0)) (g.val w) x = siegel (formB 1 F) u v x
      dsimp only [w]
      rw [LinearEquiv.apply_symm_apply,← siegel_scale,← ha]
    rw [← he]
    have hg : g ∈ (toOrthogonal (F := F)).range := ⟨a,rfl⟩
    exact (toOrthogonal (F := F)).range.mul_mem
      ((toOrthogonal (F := F)).range.mul_mem hg hs) ((toOrthogonal (F := F)).range.inv_mem hg)

theorem toOrthogonal_range : (toOrthogonal (F := F)).range = elementarySubgroup (formB 1 F) := by
  apply le_antisymm
  · rintro g ⟨a,rfl⟩
    exact toOrthogonal_mem_elementary a
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨u,v,hu,huv,rfl⟩
    exact siegel_mem_image u v hu huv

end ClassicalOrthogonal.RankOneComparison
