module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortCentralizer

/-!
# Conjugators of native short plane parameters

A projective conjugator between nonsingular central plane parameters
preserves their common displacement plane. Equality of their involutory
SU lifts follows from the actual central kernel of order five; displacement
transport then places the conjugator in the plane parabolic.

This supplies the inner factor in the full-extension short-centralizer
argument, Aschbacher–Smith F.4.27(4) and F.4.42, pp.288,295.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem project_injective_square_one (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    (A B : J.specialSubgroup) (hA : A^2 = 1) (hB : B^2 = 1)
    (he : project J A = project J B) : A = B := by
  have hfour : B^4=1 := by rw [show 4=2*2 by decide,pow_mul,hB,one_pow]
  have hc : Commute A B := RadicalCentralizers.commute_of_project_commute_fourth_power J hconj hcard
    (by rw [he]) hfour
  let C := A * B⁻¹
  have hker : C ∈ (project J).ker := by simp [C,MonoidHom.mem_ker,he]
  have htwo : C^2=1 := by rw [hc.inv_right.mul_pow,hA,inv_pow,hB]; simp
  have hfive : C^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨C,hker⟩ : (project J).ker))
    rw [card_project_kernel J hconj hcard] at hh
    exact congrArg Subtype.val hh
  have hC : C=1 := calc
    C = (C^2)^2*C := by rw [htwo]; simp
    _ = C^5 := by group
    _ = 1 := hfive
  exact mul_inv_eq_one.mp hC

/-- A projective conjugator between nonsingular central plane parameters
preserves their common displacement plane. -/
theorem nonsingular_conjugator_mem_plane (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (u v : PlaneCore.Parameters J) (hu : u.x = 0) (hv : v.x = 0)
    (hdu : u.z.det ≠ 0) (hdv : v.z.det ≠ 0)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g * (PlaneCore.Parameters.toParabolic hJ u).val * g⁻¹ =
      (PlaneCore.Parameters.toParabolic hJ v).val) : g ∈ planeParabolic J := by
  obtain ⟨A,rfl⟩ := project_surjective J g
  have hsu : (PlaneCore.Parameters.toSU hJ u)^2=1 := by
    rw [←map_pow,(PlaneCore.Parameters.square_eq_one_iff J u).mpr hu,map_one]
  have hsv : (PlaneCore.Parameters.toSU hJ v)^2=1 := by
    rw [←map_pow,(PlaneCore.Parameters.square_eq_one_iff J v).mpr hv,map_one]
  change project J A * project J (PlaneCore.Parameters.toSU hJ u) * (project J A)⁻¹ =
    project J (PlaneCore.Parameters.toSU hJ v) at hg
  have he : A * PlaneCore.Parameters.toSU hJ u * A⁻¹ = PlaneCore.Parameters.toSU hJ v :=
    project_injective_square_one J hcard hconj _ _
      (by rw [conj_pow,hsu]; simp) hsv (by simpa only [map_mul,map_inv] using hg)
  have hcomm : A * PlaneCore.Parameters.toSU hJ u = PlaneCore.Parameters.toSU hJ v * A :=
    (mul_inv_eq_iff_eq_mul).mp he
  refine ⟨A,IsotropicGeometry.mem_specialStabilizer_of_preserves J (plane F) A ?_,rfl⟩
  intro w hw
  rw [←nonsingular_displacement_eq_plane J hJ u hu hdu] at hw
  obtain ⟨y,rfl⟩ := hw
  rw [←nonsingular_displacement_eq_plane J hJ v hv hdv]
  refine ⟨linearAction J A y,?_⟩
  change linearAction J (PlaneCore.Parameters.toSU hJ v) (linearAction J A y) - linearAction J A y =
    linearAction J A (linearAction J (PlaneCore.Parameters.toSU hJ u) y - y)
  rw [map_sub]
  have hh := congrArg (fun a => linearAction J a y) hcomm
  simpa only [map_mul,LinearEquiv.mul_apply] using congrArg (fun z => z-linearAction J A y) hh.symm

end Theory.SpecificGroups.UnitaryFive.InvolutionGeometry
