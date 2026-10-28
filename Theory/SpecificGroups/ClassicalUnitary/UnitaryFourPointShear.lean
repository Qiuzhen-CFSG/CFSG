module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical

/-!
# A marked middle shear in the unitary point parabolic

The Hermitian plane parameter diag(0,1) gives the middle transvection in
SU4 over a finite field of characteristic two. It is an involution outside
the Heisenberg point radical. All its displacements in that radical have
square one, and its fixed radical elements lie in the same plane radical.
The proof uses the literal four-by-four matrices and retains both embeddings.

These are the matrix inputs for the binary point comparison in
Aschbacher--Smith 13.5.17 and F.4.27, printed pp.922 and287.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointShear
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPlaneRadical
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "R" => UnitaryFourPointLocal.radical F σ hσ

/-- The lower diagonal Hermitian parameter, whose unipotent is a middle shear. -/
def parameter : hermitianMatrices F σ := ⟨!![0,0;0,1], by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjoint]⟩

def element : P := ⟨unipotentSU F σ hσ (parameter F σ), by
  rw [mem_pointParabolicSU]
  simp [unipotentSU, unipotentMatrix, parameter]⟩

theorem element_sq : element F σ hσ ^ 2 = 1 := by
  apply Subtype.ext
  exact congrArg (fun r : UnitaryFourPlaneRadical.radical F σ hσ => r.val.val)
    (radical_sq F σ hσ (radicalEquiv F σ hσ (Multiplicative.ofAdd (parameter F σ))))

/-- The middle shear does not belong to the embedded point radical. -/
theorem element_not_mem_radical : element F σ hσ ∉
    (UnitaryFourPointLocal.radical F σ hσ).map
      (inclusion (localSU_le_pointParabolicSU F (form F σ hσ))) := by
  rintro ⟨r,hr,he⟩
  have hzero := ((UnitaryFourPointLocal.mem_radical F σ hσ r).mp hr).2.1
  have hone := congrArg (fun x : P => x.val.val.val 1 2) he
  change r.val.val.val 1 2 = 1 at hone
  exact zero_ne_one (hzero.symm.trans hone)

/-- Every plane-radical matrix fixes the first isotropic vector. -/
theorem planeRadical_le_point :
    (UnitaryFourPlaneRadical.radical F σ hσ).map
      (UnitaryFourPlaneLocal.localFactor F (form F σ hσ)).subtype ≤ P := by
  rintro x ⟨r,hr,rfl⟩
  obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨r,hr⟩
  have he := congrArg (fun a : UnitaryFourPlaneRadical.radical F σ hσ => a.val.val) hX
  change r.val ∈ P
  change _ = r.val at he
  rw [←he,mem_pointParabolicSU]
  simp [radicalEquiv,unipotent,unipotentSU,unipotentMatrix]

/-- The same shear belongs to the actual plane radical. -/
theorem element_mem_planeRadical : (element F σ hσ).val ∈
    (UnitaryFourPlaneRadical.radical F σ hσ).map
      (UnitaryFourPlaneLocal.localFactor F (form F σ hσ)).subtype :=
  ⟨(radicalEquiv F σ hσ (Multiplicative.ofAdd (parameter F σ))).val,
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (parameter F σ))).property,rfl⟩

/-- A fixed point-radical element lies in the same marked plane radical. -/
theorem fixed_radical_mem_plane (r : R)
    (hc : Commute (element F σ hσ).val r.val.val) :
    r.val.val ∈ (UnitaryFourPlaneRadical.radical F σ hσ).map
      (UnitaryFourPlaneLocal.localFactor F (form F σ hσ)).subtype := by
  obtain ⟨c,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
  apply UnitaryFourInvolutionPlacement.radical_y_zero_mem_plane F σ hσ c
  have he := congrArg (fun g : SU F (form F σ hσ) => g.val.val 1 3) hc.eq
  change (unipotentMatrix F (parameter F σ).val * radicalMatrix F σ c) 1 3 =
    (radicalMatrix F σ c * unipotentMatrix F (parameter F σ).val) 1 3 at he
  simpa [unipotentMatrix,parameter,radicalMatrix,Matrix.mul_apply,
    Fin.sum_univ_succ] using he

/-- Every displacement of this shear in the Heisenberg radical is an involution. -/
theorem displacement_sq (r : R) :
    (((element F σ hσ : P) : SU F (form F σ hσ)) * r.val.val *
      ((element F σ hσ : P) : SU F (form F σ hσ))⁻¹ * r.val.val⁻¹)^2 = 1 := by
  let v : SU F (form F σ hσ) := (element F σ hσ).val
  have hv2 : v^2=1 := congrArg Subtype.val (element_sq F σ hσ)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv2)
  let a := v * r.val.val * v⁻¹
  have hc : Commute a r.val.val := by
    obtain ⟨c,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
    dsimp only [Commute, SemiconjBy, a]
    rw [hvi]
    apply Subtype.ext
    apply Units.ext
    change (unipotentMatrix F (parameter F σ).val * radicalMatrix F σ c *
      unipotentMatrix F (parameter F σ).val) * radicalMatrix F σ c =
      radicalMatrix F σ c * (unipotentMatrix F (parameter F σ).val *
        radicalMatrix F σ c * unipotentMatrix F (parameter F σ).val)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentMatrix,parameter,radicalMatrix,Matrix.mul_apply,
        Fin.sum_univ_succ,CharTwo.add_self_eq_zero] <;> ring
  have hs : a^2=r.val.val^2 := by
    obtain ⟨c,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
    dsimp only [a]
    rw [hvi]
    apply Subtype.ext
    apply Units.ext
    change (unipotentMatrix F (parameter F σ).val * radicalMatrix F σ c *
      unipotentMatrix F (parameter F σ).val)^2 = (radicalMatrix F σ c)^2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentMatrix,parameter,radicalMatrix,Matrix.mul_apply,pow_two,
        Fin.sum_univ_succ,CharTwo.add_self_eq_zero]
    ring_nf
    simp [CharTwo.two_eq_zero]
  change (a*r.val.val⁻¹)^2=1
  rw [hc.inv_right.mul_pow,inv_pow,hs,mul_inv_cancel]
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointShear
