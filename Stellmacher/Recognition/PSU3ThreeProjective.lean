module

public import ABG.Basic

/-!
# PGU₃(3) and PSU₃(3) in the same matrix convention

The image of the full unitary isometry group in PGL equals the image of its
special unitary subgroup. Indeed the determinant d of a unitary matrix
satisfies d⁴ = 1. Multiplication by the scalar d preserves the Hermitian form,
has determinant d³d = 1, and does not change the projective class.

This makes explicit the PGU-to-PSU step in Suzuki's recognition theorem at
q = 3, using ABG's identity Gram matrix and cube Frobenius throughout.
Source: M. Suzuki, J. Algebra 2 (1965), p. 1 (definition of U₃(q)); the
scalar adjustment is the standard determinant argument for gcd(3, q+1) = 1.
-/

namespace Stellmacher.Recognition

open Matrix BenderSuzuki.MatrixGroups
local notation "E" => GaloisField 3 2
local notation "J" => ABG.unitaryForm 3 3 1 (by decide)

/-- The determinant of a unitary 3-by-3 matrix over F₉ has norm one. -/
public theorem unitaryThree_det_four (A : GL (Fin 3) E) (hA : A ∈ (J).unitarySubgroup) :
    ((GeneralLinearGroup.det A : Eˣ) : E) ^ 4 = 1 := by
  have hdet := congrArg Matrix.det ((J).mem_unitarySubgroup_iff A |>.mp hA)
  change ((J).conjTranspose (A : Matrix (Fin 3) (Fin 3) E) * 1 *
    (A : Matrix (Fin 3) (Fin 3) E)).det = (1 : Matrix (Fin 3) (Fin 3) E).det at hdet
  have hadj : (J).conjTranspose (A : Matrix (Fin 3) (Fin 3) E) =
      ((A : Matrix (Fin 3) (Fin 3) E).map (J).conj).transpose := rfl
  have hmap := RingEquiv.map_det (J).conj (A : Matrix (Fin 3) (Fin 3) E)
  change (J).conj (A : Matrix (Fin 3) (Fin 3) E).det =
    ((A : Matrix (Fin 3) (Fin 3) E).map (J).conj).det at hmap
  rw [hadj, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hmap] at hdet
  simpa [ABG.unitaryForm, iterateFrobeniusEquiv_def, frobenius_def, pow_succ] using hdet

private theorem unitaryThree_scalar_mem (d : Eˣ) (hd : (d : E) ^ 4 = 1) :
    GeneralLinearGroup.scalar (Fin 3) d ∈ (J).unitarySubgroup := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change (J).conjTranspose (Matrix.scalar (Fin 3) (d : E)) * 1 *
    Matrix.scalar (Fin 3) (d : E) = 1
  have hc : (J).conjTranspose (Matrix.scalar (Fin 3) (d : E)) =
      Matrix.scalar (Fin 3) ((d : E) ^ 3) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [HermitianForm.conjTranspose, Matrix.scalar_apply, ABG.unitaryForm,
        frobenius_def]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hc]
  simp only [mul_one]
  rw [← map_mul (Matrix.scalar (Fin 3))]
  exact (congrArg (Matrix.scalar (Fin 3)) (by simpa only [pow_succ] using hd)).trans
    (map_one (Matrix.scalar (Fin 3)))

/-- Every full unitary isometry has a special unitary representative of its
projective class, explicitly obtained by multiplying by its determinant. -/
public theorem unitaryThree_exists_special (A : GL (Fin 3) E)
    (hA : A ∈ (J).unitarySubgroup) :
    ∃ B ∈ (J).specialSubgroup, ProjGenLinGroup.mk B = ProjGenLinGroup.mk A := by
  let d := GeneralLinearGroup.det A
  have hd : (d : E) ^ 4 = 1 := unitaryThree_det_four A hA
  have hdu : d ^ 4 = 1 := Units.ext (by simpa using hd)
  let B := GeneralLinearGroup.scalar (Fin 3) d * A
  have hB : B ∈ (J).unitarySubgroup :=
    (J).unitarySubgroup.mul_mem (unitaryThree_scalar_mem d hd) hA
  refine ⟨B, (HermitianForm.mem_specialSubgroup_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (HermitianForm.mem_unitarySubgroup_iff _ _).mp hB
  · change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) d * A) = 1
    rw [map_mul, GeneralLinearGroup.det_scalar]
    change d ^ 3 * d = 1
    exact (pow_succ d 3).symm.trans hdu
  · simp [B, map_mul, ProjGenLinGroup.mk_scalar]

/-- PGU₃(3), as the projective image of the full unitary isometry group. -/
public noncomputable abbrev PGU3Three : Subgroup (ProjGenLinGroup (Fin 3) E) :=
  (J).unitarySubgroup.map ProjGenLinGroup.mk

/-- At q = 3 the full and special unitary projective images coincide. -/
public theorem pgu3Three_eq_psu3Three : PGU3Three = ABG.PSU3 3 1 (by decide) := by
  apply le_antisymm
  · rintro x ⟨A, hA, rfl⟩
    obtain ⟨B, hB, he⟩ := unitaryThree_exists_special A hA
    exact ⟨B, hB, he⟩
  · exact Subgroup.map_mono (HermitianForm.specialSubgroup_le_unitarySubgroup _)

/-- The explicit PGU₃(3)-to-PSU₃(3) identification used after recognition. -/
public noncomputable def pgu3ThreeEquivPSU3Three :
    PGU3Three ≃* ABG.PSU3 3 1 (by decide) :=
  MulEquiv.subgroupCongr pgu3Three_eq_psu3Three

end Stellmacher.Recognition
