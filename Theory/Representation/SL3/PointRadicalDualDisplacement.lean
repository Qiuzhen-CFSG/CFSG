module
public import Theory.Representation.SL3.PointLocalFixed
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed

/-!
# Point-radical fixed vectors are point-local displacements on the doubled dual

The first-row transvections force a radical-fixed covector to annihilate the
first coordinate point. Conversely, displacements by those transvections
supply both remaining coordinate axes, independently in each dual summand.
Thus every additive subgroup containing the point-local displacements
contains the full radical-fixed space. The statement retains the original
point-local and dual-action conventions over an arbitrary field.

The nonblock source application puts the original Q-elements fixed modulo
Z(Q) by the whole radical into the original secondary residual K₂.
Source: Aschbacher--Smith, C.1.34(3) and the conclusion of 4.3.2,
printed pp.136--137, 618--619; elementary SL₃ transvection calculations.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

private theorem dual_transvection_coordinates {i j : Fin 3} (hij : i ≠ j)
    (a : F) (f : Module.Dual F (Fin 3 → F)) :
    dualVectorCoordinates ((specialLinearNatural 3).dual (transvection hij a) f) =
      dualVectorCoordinates f + Pi.single j (-a * dualVectorCoordinates f i) := by
  rw [dualVectorCoordinates_action,transvection_inv]
  ext k
  simp [transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

/-- A covector fixed by the point radical annihilates the defining point. -/
theorem pointRadical_dual_fixed_coordinate (f : Module.Dual F (Fin 3 → F))
    (hf : ∀ g : pointRadicalSL F, (specialLinearNatural 3).dual g.val.val f = f) :
    dualVectorCoordinates f 0 = 0 := by
  let g := transvection (by decide : (0 : Fin 3) ≠ 1) (1:F)
  have hg : g ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [g,transvection_coe]
  have hr : (⟨g,hg⟩ : pointLocalSL F) ∈ pointRadicalSL F := by
    rw [mem_pointRadicalSL_iff]
    simp [g,transvection_coe]
  have hh := congrArg (fun u => dualVectorCoordinates u 1) (hf ⟨⟨g,hg⟩,hr⟩)
  change dualVectorCoordinates ((specialLinearNatural 3).dual g f) 1 = _ at hh
  rw [dual_transvection_coordinates] at hh
  simpa using hh

/-- Point-local displacements generate every radical-fixed vector on the doubled dual. -/
theorem doubledDual_pointRadical_fixed_mem
    (B : AddSubgroup (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hB : ∀ g ∈ pointLocalSL F, ∀ v,
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) g v - v ∈ B)
    (v : Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))
    (hv : ∀ g : pointRadicalSL F,
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) g.val.val v = v) :
    v ∈ B := by
  let e := (dualVectorCoordinates (F := F)).prodCongr dualVectorCoordinates
  have hz₁ : dualVectorCoordinates v.1 0 = 0 :=
    pointRadical_dual_fixed_coordinate v.1 (fun g => congrArg Prod.fst (hv g))
  have hz₂ : dualVectorCoordinates v.2 0 = 0 :=
    pointRadical_dual_fixed_coordinate v.2 (fun g => congrArg Prod.snd (hv g))
  have haxis (j : Fin 3) (hj : j ≠ 0) (a b : F) :
      e.symm (Pi.single j a,Pi.single j b) ∈ B := by
    let g := transvection (Ne.symm hj) (-1:F)
    have hg : g ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      simp [g,transvection_coe,hj]
    let w := e.symm (Pi.single 0 a,Pi.single 0 b)
    have hh := hB g hg w
    convert hh using 1
    apply e.injective
    rw [e.apply_symm_apply,map_sub]
    change (Pi.single j a,Pi.single j b) =
      (dualVectorCoordinates ((specialLinearNatural 3).dual g w.1),
        dualVectorCoordinates ((specialLinearNatural 3).dual g w.2)) - e w
    rw [dual_transvection_coordinates,dual_transvection_coordinates]
    have hw : e w = (Pi.single 0 a,Pi.single 0 b) := e.apply_symm_apply _
    have hw₁ := congrArg Prod.fst hw
    have hw₂ := congrArg Prod.snd hw
    change dualVectorCoordinates w.1 = _ at hw₁
    change dualVectorCoordinates w.2 = _ at hw₂
    rw [hw₁,hw₂,hw]
    simp
  have he : e v = (Pi.single 1 (dualVectorCoordinates v.1 1),
      Pi.single 1 (dualVectorCoordinates v.2 1)) +
      (Pi.single 2 (dualVectorCoordinates v.1 2),
      Pi.single 2 (dualVectorCoordinates v.2 2)) := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [e,hz₁,hz₂]
  rw [←e.symm_apply_apply v,he,map_add]
  exact B.add_mem (haxis 1 (by decide) _ _) (haxis 2 (by decide) _ _)
end Representation.SL3ParabolicNatural
