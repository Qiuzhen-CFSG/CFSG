module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel

/-!
# The scalar kernel of the full plane Levi

For fourth-power conjugation the full GL₂ Levi becomes projectively trivial
precisely on scalar fifth roots of unity. The special-linear Levi has already
been proved faithful. These are different projective-kernel assertions.

Source: the unitary parabolic calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Scalar fifth roots in the actual two-dimensional general linear group. -/
def planeScalarRoots : Subgroup (GL (Fin 2) F) :=
  ((GeneralLinearGroup.scalar (Fin 2)).comp (rootsOfUnity 5 F).subtype).range

omit [CharP F 2] in
/-- In the corrected basis each fifth-root scalar remains the same scalar. -/
theorem planeBlockGL_scalar (hconj : ∀ x, J.conj x = x ^ 4) (u : rootsOfUnity 5 F) :
    planeBlockGL J (GeneralLinearGroup.scalar (Fin 2) u.val) =
      GeneralLinearGroup.scalar (Fin 5) u.val := by
  have hu : (u.val : F) ^ 5 = 1 := (mem_rootsOfUnity' 5 u.val).mp u.property
  have h4 : (u.val : F) ^ 4 = (u.val : F)⁻¹ := by
    apply mul_right_cancel₀ u.val.ne_zero
    rw [← pow_succ, hu, inv_mul_cancel₀ u.val.ne_zero]
  have hci : J.conj ((u.val : F)⁻¹) = (u.val : F) := by
    rw [map_inv₀, hconj, h4, inv_inv]
  have hd : (GeneralLinearGroup.scalar (Fin 2) u.val).val.det = (u.val : F) ^ 2 := by
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.det_diagonal]
  have hm : planeMiddleScalar J (GeneralLinearGroup.scalar (Fin 2) u.val) = (u.val : F) := by
    unfold planeMiddleScalar
    rw [hd, hconj, ← pow_mul]
    apply mul_right_cancel₀ (pow_ne_zero 2 u.val.ne_zero)
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 u.val.ne_zero), mul_one]
    calc
      (u.val : F) ^ (2 * 4) = (u.val : F) ^ 5 * (u.val : F) ^ 3 := by ring
      _ = (u.val : F) * (u.val : F) ^ 2 := by rw [hu]; ring
  have hi : (GeneralLinearGroup.scalar (Fin 2) u.val).inv =
      (GeneralLinearGroup.scalar (Fin 2) u.val⁻¹).val :=
    congrArg Units.val (map_inv (GeneralLinearGroup.scalar (Fin 2)) u.val).symm
  apply Units.ext
  change planeBlockMatrix J (GeneralLinearGroup.scalar (Fin 2) u.val) = _
  simp only [planeBlockMatrix, hi, hm, planeAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-map_inv, GeneralLinearGroup.coe_scalar, Matrix.scalar, hci]

/-- The projective full Levi has precisely the fifth-root scalar kernel. -/
theorem planeLeviParabolic_ker (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    (planeLeviParabolic J c hc hJ).ker = planeScalarRoots (F := F) := by
  ext A
  constructor
  · intro hA
    have hp : project J (planeLeviSU J c hc hJ A) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hA)
    have hs : ProjGenLinGroup.mk (planeLeviGL J c A) = 1 :=
      congrArg Subtype.val hp
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs
    obtain ⟨a, ha⟩ := hs
    have hb := (planeLeviGL_eq_scalar_iff J c A a).mp ha.symm
    have hd := (J.mem_specialSubgroup_iff (planeLeviGL J c A)).mp
      (planeLeviGL_mem_special J c hc hJ A) |>.2
    rw [← ha, GeneralLinearGroup.det_scalar] at hd
    have hr : a ∈ rootsOfUnity 5 F := (mem_rootsOfUnity 5 a).mpr (by simpa using hd)
    refine ⟨⟨a, hr⟩, ?_⟩
    change GeneralLinearGroup.scalar (Fin 2) a = A
    apply Units.ext
    ext i j
    have he := congrArg (fun B : GL (Fin 5) F => B.val (Fin.castAdd 3 i) (Fin.castAdd 3 j)) hb
    fin_cases i <;> fin_cases j <;>
      simpa [planeBlockGL, planeBlockMatrix, GeneralLinearGroup.coe_scalar, Matrix.scalar]
        using he.symm
  · rintro ⟨u, rfl⟩
    have hb := planeBlockGL_scalar J hconj u
    have hg := (planeLeviGL_eq_scalar_iff J c _ u.val).mpr hb
    apply Subtype.ext
    apply Subtype.ext
    change ProjGenLinGroup.mk (planeLeviGL J c (GeneralLinearGroup.scalar (Fin 2) u.val)) = 1
    rw [hg]
    exact ProjGenLinGroup.mk_scalar u.val


instance planeScalarRoots_normal : (planeScalarRoots (F := F)).Normal := by
  constructor
  rintro g ⟨u, rfl⟩ x
  refine ⟨u, ?_⟩
  change GeneralLinearGroup.scalar (Fin 2) u.val =
    x * GeneralLinearGroup.scalar (Fin 2) u.val * x⁻¹
  rw [← GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]

/-- The fifth-root scalar subgroup has its usual scalar parametrization. -/
noncomputable def planeScalarRootsEquiv : rootsOfUnity 5 F ≃* planeScalarRoots (F := F) :=
  MonoidHom.ofInjective (f :=
    (GeneralLinearGroup.scalar (Fin 2)).comp (rootsOfUnity 5 F).subtype) (by
      intro u v h
      apply Subtype.ext
      apply Units.ext
      have he := congrArg (fun A : GL (Fin 2) F => A.val 0 0) h
      simpa using he)

omit [CharP F 2] in
/-- The projective scalar factor has order five over the field of order sixteen. -/
theorem planeScalarRoots_card [Finite F] (hcard : Nat.card F = 16) :
    Nat.card (planeScalarRoots (F := F)) = 5 := by
  rw [← Nat.card_congr (planeScalarRootsEquiv (F := F)).toEquiv]
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  decide

/-- The full projective Levi image, as the quotient by its actual scalar kernel. -/
noncomputable def planeLeviImageEquiv (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    (GL (Fin 2) F ⧸ planeScalarRoots (F := F)) ≃*
      (planeLeviParabolic J c hc hJ).range :=
  (QuotientGroup.quotientMulEquivOfEq (planeLeviParabolic_ker J c hc hJ hconj).symm).trans
    (QuotientGroup.quotientKerEquivRange (planeLeviParabolic J c hc hJ))

end Theory.SpecificGroups.UnitaryFive.PlaneCore
