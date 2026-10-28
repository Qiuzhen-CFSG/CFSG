/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
The normality argument is adapted from ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, Orthogonal/ElementaryNormal.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Basic
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.JointGeneration
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness of the binary minus-six elementary subgroup

Four explicit commutators of Siegel transformations give the four parameter
basis roots at a fixed singular point. The additive parameter law gives the
whole root group. Normality and reflection transport of singular vectors then
give every root, proving that the actual elementary subgroup is perfect.
Consequently it lies in the commutator subgroup of the full isometry group.

The finite certificates check only vectors in the 64-element natural space;
no full group enumeration or alternative model is used. The separately checked
coordinate formulas prevent nested expansion of the quadratic-form formula.

This is the intrinsic elementary-group input to GLS3 §2.7, for the orthogonal
section in Table 5.3o and Aschbacher--Smith A.2.19. Only the normality proof is
ported from ATLAS; the four commutator witnesses are specific to this form.
-/

@[expose] public noncomputable section

open scoped commutatorElement
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

/-- Conjugation transports both parameters of an actual Siegel transformation. -/
theorem generation_siegel_conj (g : FullGroup) (u v : NaturalSpace)
    (hu : naturalForm u = 0) (huv : naturalForm.polarBilin u v = 0) :
    g * siegelElement naturalForm u v hu huv * g⁻¹ =
      siegelElement naturalForm (g.val u) (g.val v)
        ((isometryCarrierEquiv naturalForm g).map_app u |>.trans hu)
        ((isometry_polar naturalForm (isometryCarrierEquiv naturalForm g) u v).trans huv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val (siegel naturalForm u v (g.val.symm x)) =
    siegel naturalForm (g.val u) (g.val v) x
  have h := siegel_covariant naturalForm (isometryCarrierEquiv naturalForm g) u v
    (g.val.symm x)
  change g.val (siegel naturalForm u v (g.val.symm x)) =
    siegel naturalForm (g.val u) (g.val v) (g.val (g.val.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

instance generation_elementary_normal : (elementarySubgroup naturalForm).Normal := by
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    rw [generation_siegel_conj]
    exact siegelElement_mem _ _ _ _ _
  | one => simp
  | mul x y _ _ ihx ihy =>
    have he : g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup naturalForm).mul_mem ihx ihy
  | inv x _ ih =>
    have he : g * x⁻¹ * g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup naturalForm).inv_mem ih

private abbrev elementaryDerived := ⁅elementarySubgroup naturalForm, elementarySubgroup naturalForm⁆

private def basisVector : Fin 6 → NaturalSpace :=
  ![(![(1,0),(0,0)], (0,0)), (![(0,1),(0,0)], (0,0)),
    (![(0,0),(1,0)], (0,0)), (![(0,0),(0,1)], (0,0)),
    (![(0,0),(0,0)], (1,0)), (![(0,0),(0,0)], (0,1))]
private theorem linear_ext_basis (g h : NaturalSpace →ₗ[F] NaturalSpace)
    (he : ∀ i, g (basisVector i) = h (basisVector i)) : g = h := by
  apply LinearMap.ext
  intro v
  have hv : v = (v.1 0).1 • basisVector 0 + (v.1 0).2 • basisVector 1 +
      (v.1 1).1 • basisVector 2 + (v.1 1).2 • basisVector 3 +
      v.2.1 • basisVector 4 + v.2.2 • basisVector 5 := by
    exact (by decide +kernel : ∀ v : NaturalSpace, v =
      (v.1 0).1 • basisVector 0 + (v.1 0).2 • basisVector 1 +
      (v.1 1).1 • basisVector 2 + (v.1 1).2 • basisVector 3 +
      v.2.1 • basisVector 4 + v.2.2 • basisVector 5) v
  rw [hv]
  simp only [map_add, map_smul, he]
private def leftParameter : Fin 4 → NaturalSpace :=
  ![basisVector 4, basisVector 4, basisVector 5, basisVector 4]
private def rightDirection : Fin 4 → NaturalSpace :=
  ![basisVector 2, basisVector 3, basisVector 2 + basisVector 3 + basisVector 4,
    basisVector 2 + basisVector 3 + basisVector 5]
private def rightParameter : Fin 4 → NaturalSpace :=
  ![basisVector 5, basisVector 5, basisVector 2 + basisVector 3,
    basisVector 2 + basisVector 3]
private theorem seed_conditions (i : Fin 4) :
    naturalForm (basisVector 0) = 0 ∧
    naturalForm.polarBilin (basisVector 0) (leftParameter i) = 0 ∧
    naturalForm (rightDirection i) = 0 ∧
    naturalForm.polarBilin (rightDirection i) (rightParameter i) = 0 ∧
    naturalForm.polarBilin (basisVector 0) (basisVector (i.addNat 2)) = 0 := by
  rw [naturalForm_eq]
  revert i
  decide +kernel
private def leftSeed (i : Fin 4) : FullGroup :=
  siegelElement naturalForm (basisVector 0) (leftParameter i)
    (seed_conditions i).1 (seed_conditions i).2.1
private def rightSeed (i : Fin 4) : FullGroup :=
  siegelElement naturalForm (rightDirection i) (rightParameter i)
    (seed_conditions i).2.2.1 (seed_conditions i).2.2.2.1
private def fastLeft (i : Fin 4) (x : NaturalSpace) : NaturalSpace :=
  if i = 2 then
    (![((x.1 0).1 + (x.1 0).2 + x.2.1, (x.1 0).2), x.1 1],
      (x.2.1, (x.1 0).2 + x.2.2))
  else
    (![((x.1 0).1 + (x.1 0).2 + x.2.2, (x.1 0).2), x.1 1],
      ((x.1 0).2 + x.2.1, x.2.2))
private def fastRight (i : Fin 4) (x : NaturalSpace) : NaturalSpace :=
  ![( ![x.1 0, ((x.1 1).1 + (x.1 1).2 + x.2.1, (x.1 1).2)],
        (x.2.1, (x.1 1).2 + x.2.2)),
    ( ![x.1 0, ((x.1 1).1, (x.1 1).1 + (x.1 1).2 + x.2.1)],
        (x.2.1, (x.1 1).1 + x.2.2)),
    ( ![x.1 0, ((x.1 1).2, (x.1 1).1)], (x.2.1 + x.2.2, x.2.2)),
    ( ![x.1 0, ((x.1 1).2, (x.1 1).1)], (x.2.1, x.2.1 + x.2.2))] i
private theorem left_apply (i : Fin 4) (x : NaturalSpace) :
    (leftSeed i).val x = fastLeft i x := by
  change siegel naturalForm (basisVector 0) (leftParameter i) x = _
  rw [naturalForm_eq]
  exact (by decide +kernel : ∀ (i : Fin 4) (x : NaturalSpace),
    siegel (form F 2 1) (basisVector 0) (leftParameter i) x = fastLeft i x) i x
private theorem right_apply (i : Fin 4) (x : NaturalSpace) :
    (rightSeed i).val x = fastRight i x := by
  change siegel naturalForm (rightDirection i) (rightParameter i) x = _
  rw [naturalForm_eq]
  exact (by decide +kernel : ∀ (i : Fin 4) (x : NaturalSpace),
    siegel (form F 2 1) (rightDirection i) (rightParameter i) x = fastRight i x) i x
private theorem seed_commutator (i : Fin 4) :
    ⁅leftSeed i, rightSeed i⁆ =
      siegelElement naturalForm (basisVector 0) (basisVector (i.addNat 2))
        (seed_conditions i).1 (seed_conditions i).2.2.2.2 := by
  have hi (u v : NaturalSpace) (hu : naturalForm u = 0)
      (huv : naturalForm.polarBilin u v = 0) :
      (siegelElement naturalForm u v hu huv)⁻¹ = siegelElement naturalForm u v hu huv := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel naturalForm u (-v) x = siegel naturalForm u v x
    rw [show -v = v from (by decide : ∀ v : NaturalSpace, -v = v) v]
  rw [commutatorElement_def, show (leftSeed i)⁻¹ = leftSeed i from hi _ _ _ _,
    show (rightSeed i)⁻¹ = rightSeed i from hi _ _ _ _]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linear_ext_basis
  intro j
  change (leftSeed i).val ((rightSeed i).val ((leftSeed i).val ((rightSeed i).val
    (basisVector j)))) = siegel naturalForm (basisVector 0) (basisVector (i.addNat 2)) (basisVector j)
  simp only [left_apply, right_apply, naturalForm_eq]
  exact (by decide +kernel : ∀ (i : Fin 4) (j : Fin 6),
    fastLeft i (fastRight i (fastLeft i (fastRight i (basisVector j)))) =
    siegel (form F 2 1) (basisVector 0) (basisVector (i.addNat 2)) (basisVector j)) i j
private def basePoint : Point := ⟨basisVector 0, by
  rw [naturalForm_eq]
  decide +kernel⟩

private def parameterIndex : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]
private def parameterBasis (i : Fin 5) : RootParameter basePoint :=
  ⟨basisVector (parameterIndex i), by
    change naturalForm.polarBilin (basisVector 0) (basisVector (parameterIndex i)) = 0
    rw [naturalForm_eq]
    revert i
    decide +kernel⟩
private def parameterCoefficient (v : NaturalSpace) : Fin 5 → F :=
  ![(v.1 0).1, (v.1 1).1, (v.1 1).2, v.2.1, v.2.2]

private theorem parameter_expansion (v : RootParameter basePoint) :
    v = ∑ i, parameterCoefficient v.val i • parameterBasis i := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hv : naturalForm.polarBilin (basisVector 0) v.val = 0 := v.prop
  rw [naturalForm_eq] at hv
  exact (by decide +kernel : ∀ v : NaturalSpace,
    (form F 2 1).polarBilin (basisVector 0) v = 0 →
      v = ∑ i : Fin 5, parameterCoefficient v i • basisVector (parameterIndex i)) v.val hv

private theorem parameterBasis_mem (i : Fin 5) :
    rootHom basePoint (Multiplicative.ofAdd (parameterBasis i)) ∈ elementaryDerived := by
  have hs (j : Fin 4) :
      siegelElement naturalForm (basisVector 0) (basisVector (j.addNat 2))
        (seed_conditions j).1 (seed_conditions j).2.2.2.2 ∈ elementaryDerived := by
    rw [← seed_commutator]
    exact Subgroup.commutator_mem_commutator
      (siegelElement_mem _ _ _ _ _) (siegelElement_mem _ _ _ _ _)
  fin_cases i
  · have he : rootHom basePoint (Multiplicative.ofAdd (parameterBasis 0)) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel naturalForm (basisVector 0) (basisVector 0) x = x
      have h := siegel_parameter_mod_line naturalForm (basisVector 0) 0 x 1
        basePoint.prop.2 (by simp)
      simpa only [one_smul, zero_add, siegel_zero] using h
    change rootHom basePoint (Multiplicative.ofAdd (parameterBasis 0)) ∈ elementaryDerived
    rw [he]
    exact elementaryDerived.one_mem
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3

private theorem basePoint_root_mem (v : RootParameter basePoint) :
    rootHom basePoint (Multiplicative.ofAdd v) ∈ elementaryDerived := by
  have hs (i : Fin 5) (c : F) :
      rootHom basePoint (Multiplicative.ofAdd (c • parameterBasis i)) ∈ elementaryDerived := by
    rcases (by decide : ∀ c : F, c = 0 ∨ c = 1) c with rfl | rfl
    · simpa only [zero_smul, ofAdd_zero, map_one] using elementaryDerived.one_mem
    · simpa only [one_smul] using parameterBasis_mem i
  have hsum (s : Finset (Fin 5)) :
      rootHom basePoint (Multiplicative.ofAdd
        (∑ i ∈ s, parameterCoefficient v.val i • parameterBasis i)) ∈ elementaryDerived := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, ofAdd_zero, map_one] using elementaryDerived.one_mem
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, ofAdd_add, map_mul]
      exact elementaryDerived.mul_mem (hs i _) ih
  rw [parameter_expansion v]
  exact hsum Finset.univ

/-- Every root lies in the derived subgroup of the elementary group itself. -/
theorem siegel_mem_elementaryDerived (u v : NaturalSpace)
    (hu : naturalForm u = 0) (huv : naturalForm.polarBilin u v = 0) :
    siegelElement naturalForm u v hu huv ∈
      ⁅elementarySubgroup naturalForm, elementarySubgroup naturalForm⁆ := by
  by_cases hu0 : u = 0
  · subst u
    have he : siegelElement naturalForm 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel naturalForm 0 v x = x
      simp [siegel]
    rw [he]
    exact elementaryDerived.one_mem
  · have hrad : naturalForm.radical = ⊥ := by
      apply bot_unique
      intro x hx
      rw [Submodule.mem_bot]
      apply (quadraticForm_nonsingular F 3).1 x
      intro w
      exact LinearMap.congr_fun hx.2 w
    obtain ⟨g, _, hgu⟩ := reflectionSubgroup_singular_transport naturalForm hrad
      basePoint.val u basePoint.prop.1 hu0 basePoint.prop.2 hu
    let w : RootParameter basePoint := ⟨g.val.symm v, by
      change naturalForm.polarBilin basePoint.val (g.val.symm v) = 0
      have hp := isometry_polar naturalForm (isometryCarrierEquiv naturalForm g)
        basePoint.val (g.val.symm v)
      change naturalForm.polarBilin (g.val basePoint.val) (g.val (g.val.symm v)) = _ at hp
      rw [hgu, LinearEquiv.apply_symm_apply, huv] at hp
      exact hp.symm⟩
    have hm := (inferInstance : elementaryDerived.Normal).conj_mem
      (rootHom basePoint (Multiplicative.ofAdd w)) (basePoint_root_mem w) g
    have he : g * rootHom basePoint (Multiplicative.ofAdd w) * g⁻¹ =
        siegelElement naturalForm u v hu huv := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change g.val (siegel naturalForm basePoint.val (g.val.symm v) (g.val.symm x)) =
        siegel naturalForm u v x
      have hc := siegel_covariant naturalForm (isometryCarrierEquiv naturalForm g)
        basePoint.val (g.val.symm v) (g.val.symm x)
      change g.val (siegel naturalForm basePoint.val (g.val.symm v) (g.val.symm x)) =
        siegel naturalForm (g.val basePoint.val) (g.val (g.val.symm v))
          (g.val (g.val.symm x)) at hc
      simpa only [hgu, LinearEquiv.apply_symm_apply] using hc
    exact he ▸ hm

/-- The actual elementary subgroup is perfect, by four binary root identities. -/
theorem elementary_perfect : Group.IsPerfect (elementarySubgroup naturalForm) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_elementaryDerived u v hu huv

/-- Siegel transformations belong to the literal full-group commutator subgroup. -/
theorem elementary_le_commutator : elementarySubgroup naturalForm ≤ commutator FullGroup := by
  let := elementary_perfect
  rw [← Subgroup.commutator_eq_self (H := elementarySubgroup naturalForm)]
  exact Subgroup.commutator_mono le_top le_top


end ClassicalOrthogonal.Minus.BinarySixObstruction
