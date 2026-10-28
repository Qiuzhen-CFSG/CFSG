module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.PointResidual
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration.ParabolicCore

/-!
# Natural action of the original point-parabolic solvable residual

For a finite field with at least four elements, the full point parabolic
has solvable residual equal to the vector stabilizer. Three transvection
differences span its natural module, even as an additive group; two
transvections determine its fixed line. An actual special-linear change
of coordinates transports both calculations to the marked point.
ResidualAction applies these facts to the original Chapter 11 residual.

Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed p.782.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3.PointRadicalGeneration Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {F : Type*} [Field F]

private def shear01 : SL(3,F) := SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) 1
private def shear12 : SL(3,F) := SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide) 1
private def shear21 : SL(3,F) := SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide) 1

private theorem shear01_mem : shear01 (F := F) ∈ pointLocalSL F := by
  rw [mem_pointLocalSL_iff]
  simp [shear01, SpecialLinearGroup.transvection_coe]
private theorem shear12_mem : shear12 (F := F) ∈ pointLocalSL F := by
  rw [mem_pointLocalSL_iff]
  simp [shear12, SpecialLinearGroup.transvection_coe]
private theorem shear21_mem : shear21 (F := F) ∈ pointLocalSL F := by
  rw [mem_pointLocalSL_iff]
  simp [shear21, SpecialLinearGroup.transvection_coe]

private theorem local_natural_full (C : AddSubgroup (Fin 3 → F))
    (hc : ∀ a ∈ pointLocalSL F, ∀ v : Fin 3 → F, a.val *ᵥ v - v ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  have h0 := hc shear01 shear01_mem ![0,v 0,0]
  have h1 := hc shear12 shear12_mem ![0,0,v 1]
  have h2 := hc shear21 shear21_mem ![0,v 2,0]
  have he : (shear01 (F := F)).val *ᵥ ![0,v 0,0] - ![0,v 0,0] +
      ((shear12 (F := F)).val *ᵥ ![0,0,v 1] - ![0,0,v 1]) +
      ((shear21 (F := F)).val *ᵥ ![0,v 2,0] - ![0,v 2,0]) = v := by
    simp only [shear01, shear12, shear21, SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    ext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  exact he ▸ C.add_mem (C.add_mem h0 h1) h2

private theorem local_natural_fixed (v : Fin 3 → F) :
    (∀ a ∈ pointLocalSL F, a.val *ᵥ v = v) ↔ v ∈ standardPoint := by
  constructor
  · intro h
    have h1 := congrFun (h shear01 shear01_mem) 0
    have h2 := congrFun (h shear12 shear12_mem) 1
    simp [shear01, shear12, SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact (mem_standardPoint v).mpr ⟨h1,h2⟩
  · intro hv a ha
    obtain ⟨h1,h2⟩ := (mem_standardPoint v).mp hv
    obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F a).mp ha
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,h1,h2,h00,h10,h20]

variable [Finite F]

/-- The full point-parabolic solvable residual, in the original right-conjugation convention. -/
theorem parabolic_residual_conjugate (hF : 4 ≤ Nat.card F) (s : SL(3,F)) :
    residualIn (parabolic (conjugatePoint (standardPoint (F := F)) s)) =
      (pointLocalSL F).map (MulAut.conj s⁻¹).toMonoidHom := by
  rw [← parabolic_conjugate]
  calc
    _ = (residualIn (parabolic standardPoint)).map (MulAut.conj s⁻¹).toMonoidHom :=
      (residualIn_map (parabolic standardPoint) (MulAut.conj s⁻¹)).symm
    _ = _ := by
      rw [parabolic_standardPoint]
      exact congrArg (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom)
        (ParabolicResiduals.pointParabolicSL_residual F hF)

/-- The point-parabolic solvable residual fixes exactly the marked field line. -/
theorem parabolic_residual_fixed (hF : 4 ≤ Nat.card F)
    (P : Submodule F (Fin 3 → F)) (hP : Module.finrank F P = 1) (v : Fin 3 → F) :
    (∀ a ∈ residualIn (parabolic P), a.val *ᵥ v = v) ↔ v ∈ P := by
  obtain ⟨s,rfl⟩ := exists_standardPoint_conjugator P hP
  rw [parabolic_residual_conjugate hF, mem_conjugatePoint]
  constructor
  · intro hv
    apply (local_natural_fixed _).mp
    intro a ha
    have hh := congrArg (fun w : Fin 3 → F => s • w)
      (hv _ (mem_map_of_mem (MulAut.conj s⁻¹).toMonoidHom ha))
    change s • ((s⁻¹ * a * s⁻¹⁻¹) • v) = s • v at hh
    rw [inv_inv] at hh
    change a • (s • v) = s • v
    simpa only [mul_smul, smul_inv_smul] using hh
  · intro hv a ha
    obtain ⟨a,ha,rfl⟩ := ha
    have hh := congrArg (fun w : Fin 3 → F => s⁻¹ • w)
      ((local_natural_fixed _).mpr hv a ha)
    change s⁻¹ • (a • (s • v)) = s⁻¹ • (s • v) at hh
    change (s⁻¹ * a * s⁻¹⁻¹) • v = v
    rw [inv_inv]
    simpa only [mul_smul, inv_smul_smul] using hh

/-- Every additive quotient of the natural module fixed by the point residual is trivial. -/
theorem parabolic_residual_full (hF : 4 ≤ Nat.card F)
    (P : Submodule F (Fin 3 → F)) (hP : Module.finrank F P = 1)
    (C : AddSubgroup (Fin 3 → F))
    (hc : ∀ a ∈ residualIn (parabolic P), ∀ v : Fin 3 → F, a.val *ᵥ v - v ∈ C) :
    C = ⊤ := by
  obtain ⟨s,rfl⟩ := exists_standardPoint_conjugator P hP
  rw [parabolic_residual_conjugate hF] at hc
  let f := (SpecialLinearGroup.toLin' s⁻¹).toAddEquiv.toAddMonoidHom
  have he : C.comap f = ⊤ := by
    apply local_natural_full
    intro a ha v
    have hh := hc _ (mem_map_of_mem (MulAut.conj s⁻¹).toMonoidHom ha) (s⁻¹ • v)
    change (s⁻¹ * a * s⁻¹⁻¹) • (s⁻¹ • v) - s⁻¹ • v ∈ C at hh
    rw [inv_inv] at hh
    change s⁻¹ • (a • v - v) ∈ C
    simpa only [smul_sub, mul_smul, smul_inv_smul] using hh
  apply top_unique
  intro v _
  have hh : s • v ∈ C.comap f := he.symm ▸ AddSubgroup.mem_top _
  change s⁻¹ • (s • v) ∈ C at hh
  simpa only [inv_smul_smul] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
