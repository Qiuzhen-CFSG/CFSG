/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
The Siegel covariance and closure-normality proofs are adapted from ATLAS,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917,
Atlas/LinearGroups/Orthogonal/ElementaryNormal.lean, through CFSG's
TheoremDRootNormalizer/MinusThreeComparison/CommutatorImage/Normality.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Quotient
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
import Mathlib.Tactic.Group

/-!
# Siegel transformations on the original minus-six space

The elementary subgroup is normal in the full isometry group in every
characteristic. A root between the two displayed hyperbolic planes is
explicitly nonscalar. Consequently its image in the original orthogonal
commutator's scalar quotient is nontrivial whenever the elementary subgroup
lies in that commutator. Simplicity is used only on this projective quotient.

These are the geometric subgroup arguments needed by the odd exterior-image
comparison. They do not assume or assert any unitary lifting theorem.
Source: GLS3 §2.7 and the small orthogonal reduction in Aschbacher–Smith
A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
namespace Image
variable (F : Type) [Field F] [Finite F]

/-- The first singular coordinate direction, with the original minus form. -/
def direction : Space F 2 := (![(1, 0), (0, 0)], (0, 0))

/-- Its hyperbolic partner. -/
def opposite : Space F 2 := (![(0, 1), (0, 0)], (0, 0))

/-- A perpendicular singular direction in the second hyperbolic plane. -/
def transverse : Space F 2 := (![(0, 0), (1, 0)], (0, 0))

theorem direction_singular : quadraticForm F 3 (direction F) = 0 := by
  simp [quadraticForm, form_apply, direction, Fin.sum_univ_succ]

theorem transverse_singular : quadraticForm F 3 (transverse F) = 0 := by
  simp [quadraticForm, form_apply, transverse, Fin.sum_univ_succ]

/-- The unhalved polar pairing with the first direction is a coordinate. -/
theorem polar_direction (v : Space F 2) :
    (quadraticForm F 3).polarBilin (direction F) v = (v.1 0).2 := by
  change (form F 2 (parameter F)).polarBilin _ _ = _
  rw [form_polar, plane_polar]
  simp [direction, Fin.sum_univ_succ]

theorem direction_perp_transverse :
    (quadraticForm F 3).polarBilin (direction F) (transverse F) = 0 := by
  rw [polar_direction]
  rfl

/-- A root whose nonscalar action will survive the actual scalar quotient. -/
def witness : FullOrthogonal F :=
  siegelElement (quadraticForm F 3) (direction F) (transverse F)
    (direction_singular F) (direction_perp_transverse F)

theorem witness_mem_elementary : witness F ∈ elementarySubgroup (quadraticForm F 3) :=
  siegelElement_mem _ _ _ _ _

theorem witness_direction : (witness F).val (direction F) = direction F :=
  Quadratic.siegel_fix _ _ _ (direction_singular F) (direction_perp_transverse F)

theorem witness_opposite :
    (witness F).val (opposite F) = opposite F - transverse F := by
  change Quadratic.siegel (quadraticForm F 3) (direction F) (transverse F) (opposite F) = _
  have hu : (quadraticForm F 3).polarBilin (opposite F) (direction F) = 1 := by
    rw [Quadratic.polar_swap, polar_direction]
    rfl
  have hv : (quadraticForm F 3).polarBilin (opposite F) (transverse F) = 0 := by
    change (form F 2 (parameter F)).polarBilin _ _ = _
    rw [form_polar]
    simp [opposite, transverse, Fin.sum_univ_succ]
  simp only [Quadratic.siegel, hu, hv, transverse_singular, zero_smul, add_zero,
    one_smul, zero_mul, sub_zero]

/-- No scalar fixes the first direction and has this action on its partner. -/
theorem witness_not_scalar :
    ¬ ∃ c : F, ∀ v : Space F 2, (witness F).val v = c • v := by
  rintro ⟨c, hc⟩
  have hdir := hc (direction F)
  rw [witness_direction] at hdir
  have hc1 : (1 : F) = c := by
    have h := congrArg (fun v : Space F 2 => (v.1 0).1) hdir
    simpa [direction] using h
  have hopp := hc (opposite F)
  rw [← hc1, one_smul, witness_opposite] at hopp
  have h := congrArg (fun v : Space F 2 => (v.1 1).1) hopp
  simp [opposite, transverse] at h

/-- Every full isometry preserves the quadratic form, before taking quotients. -/
theorem form_preserved (g : FullOrthogonal F) (x : Space F 2) :
    quadraticForm F 3 (g.val x) = quadraticForm F 3 x :=
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property x

theorem polar_preserved (g : FullOrthogonal F) (u v : Space F 2) :
    (quadraticForm F 3).polarBilin (g.val u) (g.val v) =
      (quadraticForm F 3).polarBilin u v := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add, form_preserved]

/-- Conjugation transports both literal Siegel parameters. -/
theorem siegel_conj (g : FullOrthogonal F) (u v : Space F 2)
    (hu : quadraticForm F 3 u = 0) (huv : (quadraticForm F 3).polarBilin u v = 0) :
    g * siegelElement (quadraticForm F 3) u v hu huv * g⁻¹ =
      siegelElement (quadraticForm F 3) (g.val u) (g.val v)
        ((form_preserved F g u).trans hu) ((polar_preserved F g u v).trans huv) := by
  let e : (quadraticForm F 3).IsometryEquiv (quadraticForm F 3) :=
    { g.val with map_app' := form_preserved F g }
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (Quadratic.siegel (quadraticForm F 3) u v (g.val.symm x)) =
    Quadratic.siegel (quadraticForm F 3) (g.val u) (g.val v) x
  have he := Quadratic.siegel_covariant (quadraticForm F 3) e u v (g.val.symm x)
  change g.val (Quadratic.siegel (quadraticForm F 3) u v (g.val.symm x)) =
    Quadratic.siegel (quadraticForm F 3) (g.val u) (g.val v)
      (g.val (g.val.symm x)) at he
  simpa only [LinearEquiv.apply_symm_apply] using he

/-- The actual Siegel-generated subgroup is normal in the full isometry group. -/
theorem elementary_normal : (elementarySubgroup (quadraticForm F 3)).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    rw [siegel_conj]
    exact siegelElement_mem _ _ _ _ _
  | one => simp
  | mul x y _ _ ihx ihy =>
    have he : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup (quadraticForm F 3)).mul_mem ihx ihy
  | inv x _ ih =>
    have he : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup (quadraticForm F 3)).inv_mem ih

/-- Project the elementary subgroup through the original commutator and its
original scalar quotient; no replacement projective carrier is introduced. -/
def projectiveElementary : Subgroup (ClassicalGroup.POmegaMinus 3 F) :=
  ((elementarySubgroup (quadraticForm F 3)).subgroupOf
    (commutator (FullOrthogonal F))).map
      (QuotientGroup.mk' (scalarSubgroup F (Space F 2) (quadraticForm F 3)))

theorem projectiveElementary_normal : (projectiveElementary F).Normal :=
  ((elementary_normal F).subgroupOf _).map _ (QuotientGroup.mk'_surjective _)

/-- The displayed root remains nontrivial after quotienting by actual scalars. -/
theorem witness_project_ne_one (hw : witness F ∈ commutator (FullOrthogonal F)) :
    QuotientGroup.mk' (scalarSubgroup F (Space F 2) (quadraticForm F 3))
      ⟨witness F, hw⟩ ≠ 1 := by
  intro he
  obtain ⟨c, hc⟩ := (projectiveOmega_mk_eq_one_iff _ _ _ _).mp he
  exact witness_not_scalar F ⟨c, hc⟩

theorem projectiveElementary_ne_bot
    (hE : elementarySubgroup (quadraticForm F 3) ≤ commutator (FullOrthogonal F)) :
    projectiveElementary F ≠ ⊥ := by
  intro he
  have hm : QuotientGroup.mk' (scalarSubgroup F (Space F 2) (quadraticForm F 3))
      ⟨witness F, hE (witness_mem_elementary F)⟩ ∈ projectiveElementary F :=
    ⟨⟨witness F, hE (witness_mem_elementary F)⟩, witness_mem_elementary F, rfl⟩
  rw [he, Subgroup.mem_bot] at hm
  exact witness_project_ne_one F _ hm

/-- Inherited projective simplicity makes the elementary image surjective.
Simplicity of the unprojectivized orthogonal commutator is not needed. -/
theorem projectiveElementary_eq_top [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (hE : elementarySubgroup (quadraticForm F 3) ≤ commutator (FullOrthogonal F)) :
    projectiveElementary F = ⊤ :=
  (projectiveElementary_normal F).eq_bot_or_eq_top.resolve_left
    (projectiveElementary_ne_bot F hE)

end Image

open BenderSuzuki.MatrixGroups
variable {F E : Type} [Field F] [Finite F] [Field E]
variable {J : HermitianForm 4 E} (R : ExteriorRealization F E J)

/-- First-direction lifts and singular-line transport suffice to lift every
Siegel transformation. Both hypotheses concern the literal exterior action. -/
theorem ExteriorRealization.siegel_mem_range_of_direction_and_transport
    (hroot : ∀ (v : Space F 2) (hv :
        (quadraticForm F 3).polarBilin (Image.direction F) v = 0),
      siegelElement (quadraticForm F 3) (Image.direction F) v
        (Image.direction_singular F) hv ∈ R.action.range)
    (htrans : ∀ (u : Space F 2), quadraticForm F 3 u = 0 → u ≠ 0 →
      ∃ (g : J.specialSubgroup) (b : F), b ≠ 0 ∧
        (R.action g).val u = b • Image.direction F)
    (u v : Space F 2) (hu : quadraticForm F 3 u = 0)
    (huv : (quadraticForm F 3).polarBilin u v = 0) :
    siegelElement (quadraticForm F 3) u v hu huv ∈ R.action.range := by
  by_cases hu0 : u = 0
  · subst u
    have he : siegelElement (quadraticForm F 3) 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change Quadratic.siegel (quadraticForm F 3) 0 v x = x
      simp [Quadratic.siegel]
    rw [he]
    exact Subgroup.one_mem _
  obtain ⟨a, b, _, ha⟩ := htrans u hu hu0
  let g := R.action a
  have hgu : quadraticForm F 3 (g.val u) = 0 :=
    (Image.form_preserved F g u).trans hu
  have hguv : (quadraticForm F 3).polarBilin (g.val u) (g.val v) = 0 :=
    (Image.polar_preserved F g u v).trans huv
  have hv' : (quadraticForm F 3).polarBilin (Image.direction F) (b • g.val v) = 0 := by
    rw [ha, map_smul, LinearMap.smul_apply, smul_eq_mul] at hguv
    simpa only [map_smul, smul_eq_mul] using hguv
  have ht : siegelElement (quadraticForm F 3) (g.val u) (g.val v) hgu hguv =
      siegelElement (quadraticForm F 3) (Image.direction F) (b • g.val v)
        (Image.direction_singular F) hv' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change Quadratic.siegel (quadraticForm F 3) (g.val u) (g.val v) x = _
    rw [ha, Quadratic.siegel_scale]
    rfl
  have hconj : g * siegelElement (quadraticForm F 3) u v hu huv * g⁻¹ ∈
      R.action.range := by
    rw [Image.siegel_conj, ht]
    exact hroot _ hv'
  have hg : g ∈ R.action.range := ⟨a, rfl⟩
  have hm := R.action.range.mul_mem
    (R.action.range.mul_mem (R.action.range.inv_mem hg) hconj) hg
  convert hm using 1
  group

end ClassicalOrthogonal.Minus.OddSixComparison
