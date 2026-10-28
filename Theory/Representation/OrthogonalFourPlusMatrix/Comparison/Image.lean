/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.RankOne
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The determinant action has precisely the elementary orthogonal image

SL₂ transvections act as coordinate Siegel transformations, giving one
inclusion. Conversely, the rank-one matrix orbit transports any nonzero
singular vector to the standard one, whose Siegel transformations are explicit
pairs of transvections. Conjugation then gives every elementary generator.

Adapted from `Atlas/LinearGroups/Orthogonal/D2MatrixImage.lean`,
`D2MatrixSiegelImage.lean`, and the generator conjugation proof in
`ElementaryNormal.lean`. The carrier is CFSG's existing elementary subgroup.
Source application: Aschbacher–Smith 13.8.16(1), printed pp.952–953.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix ClassicalOrthogonal.Quadratic Theory.AlgebraicGroup
universe u
variable {F : Type u} [Field F]

private theorem coordinate_polar_ee (a : F) :
    (formD 2 F).polarBilin (e 0) (a • e 1) = 0 := by
  rw [map_smul,polarD_e]; simp [e]

private theorem coordinate_polar_ff (a : F) :
    (formD 2 F).polarBilin (f 0) (a • f 1) = 0 := by
  rw [map_smul,polarD_f]; simp [f]

private theorem coordinate_polar_ef (i j : Fin 2) (hij : i ≠ j) (a : F) :
    (formD 2 F).polarBilin (e i) (a • f j) = 0 := by
  rw [map_smul,polarD_f]
  simp [e,hij]

private theorem left_upper_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a,1) =
      siegelElement (formD 2 F) (e 0) (-a • e 1) (formD_e 0) (coordinate_polar_ee (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 0) (-a • e 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply]
    <;> ring

private theorem left_lower_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a,1) =
      siegelElement (formD 2 F) (f 0) (a • f 1) (formD_f 0) (coordinate_polar_ff a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (f 0) (a • f 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply]
    <;> ring

private theorem right_upper_root (a : F) :
    toOrthogonal (1,SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      siegelElement (formD 2 F) (e 1) (-a • f 0) (formD_e 1)
        (coordinate_polar_ef 1 0 (by decide) (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 1) (-a • f 0) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

private theorem right_lower_root (a : F) :
    toOrthogonal (1,SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      siegelElement (formD 2 F) (e 0) (-a • f 1) (formD_e 0)
        (coordinate_polar_ef 0 1 (by decide) (-a)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change _ = siegel (formD 2 F) (e 0) (-a • f 1) x _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      Matrix.adjugate_fin_two, formD_apply, e, f, Fin.sum_univ_two,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe,
      Matrix.vecHead, Matrix.vecTail]
    <;> ring

private theorem left_mem_elementary (A : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (A,1) ∈ elementarySubgroup (formD 2 F) := by
  apply Atlas.sl_elementary_induction (fun A => toOrthogonal (A,1) ∈ elementarySubgroup (formD 2 F))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · rw [left_upper_root]
      exact siegelElement_mem _ _ _ _ _
    · rw [left_lower_root]
      exact siegelElement_mem _ _ _ _ _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    have he : ((A*B,1) : PairSL (F := F)) = (A,1)*(B,1) := by simp
    rw [he,map_mul]
    exact Subgroup.mul_mem _ hA hB

private theorem right_mem_elementary (B : SpecialLinearGroup (Fin 2) F) :
    toOrthogonal (1,B) ∈ elementarySubgroup (formD 2 F) := by
  apply Atlas.sl_elementary_induction (fun B => toOrthogonal (1,B) ∈ elementarySubgroup (formD 2 F))
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · rw [right_upper_root]
      exact siegelElement_mem _ _ _ _ _
    · rw [right_lower_root]
      exact siegelElement_mem _ _ _ _ _
    · exact False.elim (hij rfl)
  · intro A B hA hB
    have he : ((1,A*B) : PairSL (F := F)) = (1,A)*(1,B) := by simp
    rw [he,map_mul]
    exact Subgroup.mul_mem _ hA hB

/-- The full actual left-right SL2 product image lies in the actual elementary subgroup. -/
theorem toOrthogonal_mem_elementary (g : PairSL (F := F)) :
    toOrthogonal g ∈ elementarySubgroup (formD 2 F) := by
  have he : g = (g.1,1)*(1,g.2) := by simp
  rw [he,map_mul]
  exact Subgroup.mul_mem _ (left_mem_elementary g.1) (right_mem_elementary g.2)

theorem image_le_elementary : (toOrthogonal (F := F)).range ≤ elementarySubgroup (formD 2 F) := by
  rintro _ ⟨g,rfl⟩
  exact toOrthogonal_mem_elementary g
private def carrierIsometry {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g : quadraticIsometrySubgroup Q) : Q.IsometryEquiv Q where
  __ := g.val
  map_app' := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop

private theorem siegelElement_conj {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g : quadraticIsometrySubgroup Q) (u v : V)
    (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    g * siegelElement Q u v hu huv * g⁻¹ =
      siegelElement Q (g.val u) (g.val v)
        ((carrierIsometry Q g).map_app u |>.trans hu)
        ((isometry_polar Q (carrierIsometry Q g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel Q u v (g.val.symm x)) = siegel Q (g.val u) (g.val v) x
  have h := siegel_covariant Q (carrierIsometry Q g) u v (g.val.symm x)
  change g.val (siegel Q u v (g.val.symm x)) =
    siegel Q (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The root at the fixed rank-one direction is an explicit pair of SL₂ transvections. -/
private theorem standard_siegel_image (v : VectorD 2 F)
    (hv : (formD 2 F).polarBilin (e 0) v = 0) :
    siegelElement (formD 2 F) (e 0) v (formD_e 0) hv =
      toOrthogonal (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-v (.inl 1)),
        SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (-v (.inr 1))) := by
  have hv0 : v (.inr 0) = 0 := by
    have hh := hv
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formD_apply, e, Fin.sum_univ_two] at hh
    linear_combination hh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  rcases i with i | i <;> fin_cases i
  all_goals
    change siegel (formD 2 F) (e 0) v x _ = _
    simp [siegel, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Matrix.adjugate_fin_two, formD_apply, e, Fin.sum_univ_two, hv0,
      toOrthogonal, onD, coordinates, matrixAction,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply]
    <;> ring

/-- The actual left-right matrix image transports the fixed singular vector to every nonzero singular vector. -/
private theorem singular_image_orbit (u : VectorD 2 F) (hu : u ≠ 0) (hqu : formD 2 F u = 0) :
    ∃ g : PairSL (F := F), (toOrthogonal g).val (e 0) = u := by
  have hm : coordinates u ≠ 0 := by
    intro h
    exact hu (coordinates.injective (h.trans (map_zero coordinates).symm))
  obtain ⟨A,B,h⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit (coordinates u) hm
    ((coordinates_det u).trans hqu)
  refine ⟨(A,B), ?_⟩
  apply coordinates.injective
  rw [toOrthogonal_coordinates]
  have he : coordinates (e (F := F) (0 : Fin 2)) = ComparisonAux.MatrixTwo.E11 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinates, e, ComparisonAux.MatrixTwo.E11]
  rw [he]
  exact h.symm

/-- Singular transport and the explicit standard root place every Siegel generator in the image. -/
private theorem siegel_mem_image (u v : VectorD 2 F) (hu : formD 2 F u = 0)
    (huv : (formD 2 F).polarBilin u v = 0) :
    siegelElement (formD 2 F) u v hu huv ∈ (toOrthogonal (F := F)).range := by
  by_cases hu0 : u = 0
  · have he : siegelElement (formD 2 F) u v hu huv = 1 := by
      subst u
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel (formD 2 F) 0 v x = x
      simp [siegel]
    rw [he]
    exact (toOrthogonal (F := F)).range.one_mem
  · obtain ⟨a,ha⟩ := singular_image_orbit u hu0 hu
    let g := toOrthogonal a
    change g.val (e 0) = u at ha
    let w := g.val.symm v
    have hw : (formD 2 F).polarBilin (e 0) w = 0 := by
      have hh := isometry_polar (formD 2 F) (carrierIsometry _ g) (e 0) w
      change (formD 2 F).polarBilin (g.val (e 0)) (g.val (g.val.symm v)) =
        (formD 2 F).polarBilin (e 0) w at hh
      rw [LinearEquiv.apply_symm_apply, ha, huv] at hh
      exact hh.symm
    have hs : siegelElement (formD 2 F) (e 0) w (formD_e 0) hw ∈
        (toOrthogonal (F := F)).range := by
      rw [standard_siegel_image]
      exact ⟨_,rfl⟩
    have hg : g ∈ (toOrthogonal (F := F)).range := ⟨a,rfl⟩
    have he := siegelElement_conj (formD 2 F) g (e 0) w (formD_e 0) hw
    have he' : g * siegelElement (formD 2 F) (e 0) w (formD_e 0) hw * g⁻¹ =
        siegelElement (formD 2 F) u v hu huv := by
      simpa only [ha, w, LinearEquiv.apply_symm_apply] using he
    rw [← he']
    exact (toOrthogonal (F := F)).range.mul_mem
      ((toOrthogonal (F := F)).range.mul_mem hg hs) ((toOrthogonal (F := F)).range.inv_mem hg)

/-- The whole actual elementary D₂ subgroup lies in the genuine SL₂ × SL₂ matrix image. -/
theorem elementary_le_image : elementarySubgroup (formD 2 F) ≤ (toOrthogonal (F := F)).range := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u,v,hu,huv,rfl⟩
  exact siegel_mem_image u v hu huv


end ClassicalOrthogonal.FourPlusMatrix
