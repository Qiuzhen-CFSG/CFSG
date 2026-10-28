module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.NormalizerCertificates.WordRealization
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.NormalizerCertificates.Values
import Mathlib.Tactic.FinCases

/-!
# The two additional seven-coordinate normalizers

For each of the two literal local words in `Fusion/Witnesses.lean`, checked
45 by 45 matrix products give the three intertwining equations `T N = N T'`.
Cancellation and projectivization give exactly the six prescribed images in
`Fusion/Orbit.lean`, with the convention `T^N = N⁻¹ T N`.

The linear lifts are those of `OrderCertificate.localA` and `localB`.
No order, coverage, or multiplicativity assumption is required. Original ATLAS
matrices and attribution: `refs/original/onan/README.md`; witness conventions:
`NormalizerCertificates/source/README.md`.
-/

namespace ONan.Simplicity.Seven.Fusion
open ONan.OrderCertificate
open Certificate (LinearGroup)
open NormalizerCertificate

private theorem map_word {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) (w : List ℤ) :
    f (word a b w) = word (f a) (f b) w := by
  simp only [word, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  split_ifs <;> simp_all

private theorem project_local_word (w : List ℤ) :
    Matrix.ProjGenLinGroup.mk (word linearLocalA linearLocalB w) =
      (word localA localB w).val := by
  rw [map_word, mk_linearLocalA, mk_linearLocalB]
  exact (map_word modelInclusion localA localB w).symm

private def linearNormalizer : Fin 2 → LinearGroup := ![lift_r7, lift_r16]
private def linearBasis : Fin 3 → LinearGroup := ![linearX, linearY, linearZ]
private def linearImage : Fin 2 → Fin 3 → LinearGroup :=
  ![![lift_r22, lift_r24, lift_r23], ![lift_r27, lift_r30, Certificate.lift_z2]]
private def normalizerIndex (j : Fin 2) : Fin 5 := ⟨j.val + 3, by omega⟩

private theorem project_normalizer (j : Fin 2) :
    Matrix.ProjGenLinGroup.mk (linearNormalizer j) =
      (normalizer (normalizerIndex j)).val := by
  fin_cases j
  · change Matrix.ProjGenLinGroup.mk lift_r7 = _
    rw [normalizer_word_3]
    exact project_local_word _
  · change Matrix.ProjGenLinGroup.mk lift_r16 = _
    rw [normalizer_word_4]
    exact project_local_word _

private theorem project_basis (r : Fin 3) :
    Matrix.ProjGenLinGroup.mk (linearBasis r) = (evaluate (basis r)).val := by
  fin_cases r
  · change Matrix.ProjGenLinGroup.mk linearX = (evaluate ⟨1, 0, 0⟩).val
    rw [evaluate_x]
    exact project_linearX
  · change Matrix.ProjGenLinGroup.mk linearY = (evaluate ⟨0, 1, 0⟩).val
    rw [evaluate_y]
    exact project_linearY
  · change Matrix.ProjGenLinGroup.mk linearZ =
      (generatorX ^ 0 * generatorY ^ 0 * generatorZ ^ 1).val
    simpa using project_linearZ

private theorem project_powers (a b c : ℕ) :
    Matrix.ProjGenLinGroup.mk (linearX ^ a * linearY ^ b * linearZ ^ c) =
      (generatorX ^ a * generatorY ^ b * generatorZ ^ c).val := by
  change Matrix.ProjGenLinGroup.mk (linearX ^ a * linearY ^ b * linearZ ^ c) =
    modelInclusion (generatorX ^ a * generatorY ^ b * generatorZ ^ c)
  simp only [map_mul, map_pow, project_linearX, project_linearY, project_linearZ]
  rfl

private theorem project_image (j : Fin 2) (r : Fin 3) :
    Matrix.ProjGenLinGroup.mk (linearImage j r) =
      (evaluate (generatorImage (normalizerIndex j) r)).val := by
  fin_cases j <;> fin_cases r
  · change Matrix.ProjGenLinGroup.mk lift_r22 = _
    rw [target_word_0]
    exact project_powers 4 5 6
  · change Matrix.ProjGenLinGroup.mk lift_r24 = _
    rw [target_word_1]
    exact project_powers 0 3 5
  · change Matrix.ProjGenLinGroup.mk lift_r23 = _
    rw [target_word_2]
    exact project_powers 0 0 5
  · change Matrix.ProjGenLinGroup.mk lift_r27 = _
    rw [target_word_3]
    exact project_powers 3 2 3
  · change Matrix.ProjGenLinGroup.mk lift_r30 = _
    rw [target_word_4]
    exact project_powers 5 4 5
  · change Matrix.ProjGenLinGroup.mk Certificate.lift_z2 = _
    rw [target_word_5]
    exact project_powers 0 0 2

private theorem linear_intertwining (j : Fin 2) (r : Fin 3) :
    linearBasis r * linearNormalizer j = linearNormalizer j * linearImage j r := by
  fin_cases j <;> fin_cases r
  · exact intertwining_0
  · exact intertwining_1
  · exact intertwining_2
  · exact intertwining_3
  · exact intertwining_4
  · exact intertwining_5

private theorem additional_identity (j : Fin 2) (r : Fin 3) :
    (normalizer (normalizerIndex j))⁻¹ * evaluate (basis r) *
      normalizer (normalizerIndex j) = evaluate (generatorImage (normalizerIndex j) r) := by
  have h : (linearNormalizer j)⁻¹ * linearBasis r * linearNormalizer j = linearImage j r := by
    rw [mul_assoc, linear_intertwining, inv_mul_cancel_left]
  have hp := congrArg Matrix.ProjGenLinGroup.mk h
  rw [map_mul, map_mul, map_inv, project_normalizer, project_basis, project_image] at hp
  exact Subtype.ext hp

/-- The six fixed generator-image equations for the two additional normalizer words. -/
public theorem normalizer_additional_identities :
    ∀ (j : Fin 5) (r : Fin 3), 3 ≤ j.val →
      (normalizer j)⁻¹ * evaluate (basis r) * normalizer j =
        evaluate (generatorImage j r) := by
  intro j r hj
  fin_cases j
  · change 3 ≤ 0 at hj
    omega
  · change 3 ≤ 1 at hj
    omega
  · change 3 ≤ 2 at hj
    omega
  · exact additional_identity 0 r
  · exact additional_identity 1 r

end ONan.Simplicity.Seven.Fusion
