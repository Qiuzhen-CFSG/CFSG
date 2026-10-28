module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.Geometry.QuadraticConjugacy
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# The transported and projectivized GU₂ block embedding

An actual orthonormal basis transports `diag(A, det(A)⁻¹)` into the
original special unitary group. The literal special-to-projective map
then gives a homomorphism from GU₂ onto its image in PSU₃. Its index is
odd by the single involution class, and its kernel embeds into the odd
scalar kernel of SU₃ → PSU₃.

Source: the involution-centralizer geometry of Aschbacher–Smith A.3.21(a),
printed p.55 (PDF p.66), used for the odd-parameter cases of I.1.3–4.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary.Geometry
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- Conjugation by the supplied orthonormal basis, on the actual SU groups. -/
def orthonormalSpecialEquiv (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    (identityForm (n := 3) J.conj J.conj_involutive).specialSubgroup ≃*
      J.specialSubgroup where
  toFun A := ⟨C * A.val * C⁻¹, (special_conjugate_iff J C A.val hC).2 A.property⟩
  invFun A := ⟨C⁻¹ * A.val * C, (special_conjugate_iff J C _ hC).1
    (by simp [mul_assoc])⟩
  left_inv A := by apply Subtype.ext; simp [mul_assoc]
  right_inv A := by apply Subtype.ext; simp [mul_assoc]
  map_mul' A B := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem orthonormalSpecialEquiv_apply_val (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (A : (identityForm (n := 3) J.conj J.conj_involutive).specialSubgroup) :
    (orthonormalSpecialEquiv J C hC A).val = C * A.val * C⁻¹ := by rfl

/-- The determinant-corrected block homomorphism transported to the input form. -/
def specialBlockMap (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    (identityForm (n := 2) J.conj J.conj_involutive).unitarySubgroup →*
      J.specialSubgroup :=
  (orthonormalSpecialEquiv J C hC).toMonoidHom.comp
    (SU3.blockEmbedding (identityForm (n := 3) J.conj J.conj_involutive)
      (identityForm (n := 2) J.conj J.conj_involutive) rfl rfl rfl)

/-- The map retains the actual determinant-corrected matrix and basis. -/
@[simp] theorem specialBlockMap_apply_val (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (A : (identityForm (n := 2) J.conj J.conj_involutive).unitarySubgroup) :
    (specialBlockMap J C hC A).val =
      C * SpecialLinearGroup.toGL (SL3.blockEmbedding F A.val) * C⁻¹ := by rfl

theorem specialBlockMap_injective (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    Function.Injective (specialBlockMap J C hC) :=
  (orthonormalSpecialEquiv J C hC).injective.comp
    (SU3.blockEmbedding_injective _ _ rfl rfl rfl)

/-- The literal composite with the original special-to-projective homomorphism. -/
def projectiveBlockMap (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    (identityForm (n := 2) J.conj J.conj_involutive).unitarySubgroup →*
      ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp (specialBlockMap J C hC)

@[simp] theorem projectiveBlockMap_apply_val (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (A : (identityForm (n := 2) J.conj J.conj_involutive).unitarySubgroup) :
    (projectiveBlockMap J C hC A).val =
      ProjGenLinGroup.mk
        (C * SpecialLinearGroup.toGL (SL3.blockEmbedding F A.val) * C⁻¹) := by
  change (J.specialToProjective (specialBlockMap J C hC A)).val = _
  rw [J.specialToProjective_apply_val, specialBlockMap_apply_val]

variable [Finite F]

/-- Odd index survives the actual basis transport. -/
theorem odd_index_specialBlockMap (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (hchar : (2 : F) ≠ 0) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Odd (specialBlockMap J C hC).range.index := by
  rw [specialBlockMap, MonoidHom.range_comp,
    Subgroup.index_map_of_bijective (orthonormalSpecialEquiv J C hC).bijective]
  exact odd_index_blockEmbedding _ _ rfl rfl rfl hchar q hcard hfixed

/-- Projectivization preserves odd index, by index divisibility under surjection. -/
theorem odd_index_projectiveBlockMap (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (hchar : (2 : F) ≠ 0) (q : ℕ) (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Odd (projectiveBlockMap J C hC).range.index := by
  rw [projectiveBlockMap, MonoidHom.range_comp]
  exact (odd_index_specialBlockMap J C hC hchar q hcard hfixed).of_dvd_nat
    ((specialBlockMap J C hC).range.index_map_dvd J.specialToProjective_surjective)

/-- The kernel of the surjection onto the literal projective block image is odd. -/
theorem odd_kernel_projectiveBlockMap (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    Odd (Nat.card (projectiveBlockMap J C hC).rangeRestrict.ker) := by
  rw [MonoidHom.ker_rangeRestrict]
  exact J.odd_card_specialToProjective_ker.of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective J.specialToProjective.ker
      (specialBlockMap J C hC) (specialBlockMap_injective J C hC))

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.TwoPrimary.Geometry
