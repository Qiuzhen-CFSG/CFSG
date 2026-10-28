module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.InvolutionGeometry

/-!
# Native short-root centralizers in PSU₅(4)

For a central plane parameter `(0,z)` with nonsingular Hermitian block `z`,
the displacement image is exactly the standard isotropic plane. The full
native projective centralizer therefore lies in the plane parabolic. The
identity block supplies an explicit involution with this property.

This is the native input to Aschbacher–Smith F.4.27(4) and the choice of the
short-root element at the beginning of F.4.42, printed pp.288,295. It does
not assert containment of the full extension or original ambient centralizer.
The ChapterF/6 companions retain this selected matrix and the literal marking.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

private theorem parameter_displacement (hJ : J.form = 1) (u : PlaneCore.Parameters J)
    (hu : u.x = 0) (v : Fin 5 → F) :
    linearAction J (PlaneCore.Parameters.toSU hJ u) v - v =
      let w := u.z *ᵥ ![v 0 + v 1,v 2 + v 3]
      ![w 0,w 0,w 1,w 1,0] := by
  change (PlaneCore.Parameters.ambientGL u).val *ᵥ v - v = _
  rw [PlaneCore.Parameters.ambientGL_val]
  ext i
  fin_cases i <;>
    simp [PlaneCore.Parameters.ambientMatrix,hu,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring

theorem nonsingular_displacement_eq_plane (hJ : J.form = 1) (u : PlaneCore.Parameters J)
    (hu : u.x = 0) (hd : u.z.det ≠ 0) :
    displacement J (PlaneCore.Parameters.toSU hJ u) = plane F := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    change linearAction J (PlaneCore.Parameters.toSU hJ u) v - v ∈ plane F
    rw [parameter_displacement J hJ u hu v]
    exact ⟨rfl,rfl,rfl⟩
  · intro v hv
    obtain ⟨w,hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det u.z).mpr (isUnit_iff_ne_zero.mpr hd)) ![v 0,v 2]
    refine ⟨![0,w 0,0,w 1,0],?_⟩
    change linearAction J (PlaneCore.Parameters.toSU hJ u) ![0,w 0,0,w 1,0] -
      ![0,w 0,0,w 1,0] = v
    rw [parameter_displacement J hJ u hu]
    have he : ![w 0,w 1] = w := by ext i; fin_cases i <;> simp
    change ![(u.z *ᵥ ![0+w 0,0+w 1]) 0,(u.z *ᵥ ![0+w 0,0+w 1]) 0,
      (u.z *ᵥ ![0+w 0,0+w 1]) 1,(u.z *ᵥ ![0+w 0,0+w 1]) 1,0] = v
    simp only [zero_add]
    rw [he,hw]
    change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
    ext i
    fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2]

/-- Full native centralizer placement for every nonsingular central plane parameter. -/
theorem nonsingular_centralizer_le [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (u : PlaneCore.Parameters J) (hu : u.x = 0) (hd : u.z.det ≠ 0) :
    centralizer ({(PlaneCore.Parameters.toParabolic hJ u).val} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ planeParabolic J := by
  have hs : (PlaneCore.Parameters.toSU hJ u) ^ 2 = 1 := by
    rw [←map_pow,(PlaneCore.Parameters.square_eq_one_iff J u).mpr hu,map_one]
  have hh := projective_centralizer_le_displacement J hcard hconj _ hs
  rw [nonsingular_displacement_eq_plane J hJ u hu hd] at hh
  exact hh

/-- An explicit nonsingular Hermitian plane parameter. -/
def shortParameter : PlaneCore.Parameters J where
  x := 0
  z := 1
  relation i j := by
    by_cases h : i = j
    · subst j; simp [CharTwo.add_self_eq_zero]
    · simp [h,Ne.symm h]

theorem shortParameter_ne_one : shortParameter J ≠ 1 := by
  intro hh
  have he := congrArg (fun u : PlaneCore.Parameters J => u.z 0 0) hh
  exact one_ne_zero he

theorem shortParameter_square : shortParameter J ^ 2 = 1 :=
  (PlaneCore.Parameters.square_eq_one_iff J _).mpr rfl

theorem shortParameter_det : (shortParameter J).z.det = 1 := Matrix.det_one

/-- The chosen short involution has its full native centralizer in the plane endpoint. -/
theorem short_centralizer_le [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    centralizer ({(PlaneCore.Parameters.toParabolic hJ (shortParameter J)).val} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ planeParabolic J :=
  nonsingular_centralizer_le J hcard hconj hJ _ rfl (by rw [shortParameter_det]; exact one_ne_zero)

end Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
