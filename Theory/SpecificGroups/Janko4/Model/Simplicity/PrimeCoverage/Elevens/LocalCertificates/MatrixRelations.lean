module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations.WordEvaluation

/-!
# Certified eleven-local matrix relations for J₄

The ATLAS normalizer words yield an extraspecial presentation on `localX`,
`localY`, and `localZ`, together with the six specified normalizer identities.
Each straight-line step is evaluated by a kernel-checked packed matrix product;
faithfulness of `toMatrix` then transfers the identities to `Model`. The entry
at (0,0) distinguishes the central element from the identity.

Source: ATLAS J4G1-max7W1, with attribution and the complete word transcription
in `Elevens.Words`. No assertion of simplicity or group order is used.
-/

public section
namespace Janko4.Simplicity.Elevens
open Janko4.GeneratorCertificates

namespace MatrixCertificates

/-- The generated straight-line definitions agree with the public ATLAS words. -/
lemma normalizerWords_eq {G : Type*} [Group G] (a b : G) :
    normalizerWords a b = (t35 a b, t33 a b) := rfl

lemma localX_eq {G : Type*} [Group G] (a b : G) : localX a b = x a b := rfl
lemma localY_eq {G : Type*} [Group G] (a b : G) : localY a b = y a b := rfl
lemma localZ_eq {G : Type*} [Group G] (a b : G) : localZ a b = z a b := rfl

private lemma eq_certificate {g h : Model} {rs : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows rs) : g = h :=
  toMatrix_injective (hg.trans hh.symm)

private lemma one_certificate {g : Model}
    (hg : toMatrix g = decodeRows packedOne) : g = 1 := by
  apply toMatrix_injective
  rw [hg, decode_packedOne, map_one]

end MatrixCertificates

open MatrixCertificates

/-- Kernel-certified extraspecial relations for the actual eleven-local words. -/
theorem matrix_elevenRelations (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ElevenRelations (localX (a hA) (b hB)) (localY (a hA) (b hB))
      (localZ (a hA) (b hB)) := by
  rw [localX_eq, localY_eq, localZ_eq]
  refine ⟨one_certificate (eval_x11 hA hB), one_certificate (eval_y11 hA hB),
    one_certificate (eval_z11 hA hB), ?_, ?_, rfl, ?_⟩
  · exact eq_certificate (eval_xz hA hB) (eval_zx hA hB)
  · exact eq_certificate (eval_yz hA hB) (eval_zy hA hB)
  · intro h
    have e := congrArg (fun g => toMatrix g 0 0) h
    rw [eval_z, map_one] at e
    have h0 : decodeRows zRows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
    exact h0 e

/-- Kernel-certified conjugation action of the two ATLAS normalizer words. -/
theorem matrix_elevenNormalizerRelations
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ElevenNormalizerRelations (normalizerWords (a hA) (b hB)).1
      (normalizerWords (a hA) (b hB)).2
      (localX (a hA) (b hB)) (localY (a hA) (b hB))
      (localZ (a hA) (b hB)) := by
  rw [normalizerWords_eq, localX_eq, localY_eq, localZ_eq]
  exact ⟨eq_certificate (eval_ux hA hB) (eval_rhsux hA hB),
    eq_certificate (eval_uy hA hB) (eval_rhsuy hA hB),
    eq_certificate (eval_uz hA hB) (eval_z hA hB), rfl,
    eq_certificate (eval_vy hA hB) (eval_rhsvy hA hB),
    eq_certificate (eval_vz hA hB) (eval_z6 hA hB)⟩

end Janko4.Simplicity.Elevens
