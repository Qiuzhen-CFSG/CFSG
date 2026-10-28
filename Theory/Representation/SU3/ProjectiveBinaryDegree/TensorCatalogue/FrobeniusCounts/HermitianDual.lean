module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.TensorWords
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.FrobeniusCounts.FoldedWords
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod.Coefficients
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.CharacterSeparation.FactorCharacters

/-!
# The unitary graph twist from the original Hermitian form

The Gram pairing of `J` gives an actual intertwiner from the conjugate natural
representation of `J.specialSubgroup` to its linear dual. No change to a standard
Hermitian form is needed. At the unitary exponent this identifies the coefficient
Frobenius on natural characters with duality. The adjoint character formula then
shows that the same Frobenius exchanges the natural and dual labels and fixes
the trivial and adjoint labels.

`TwistedRotation` uses these four identities at the tensor-word boundary.
Source: GLS III, Remark 2.8.8; Guralnick--Malle, §3.1, internal p.12.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/FrobeniusCounts/HermitianDual.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
variable {F K : Type*} [Field F] [Field K]

private def gramDualCoordinates (J : HermitianForm 3 F) (ι : F →+* K) :
    (Fin 3 → K) ≃ₗ[K] Module.Dual K (Fin 3 → K) :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.mkOfDetNeZero
    (J.form.map ι).transpose (by
      rw [Matrix.det_transpose]
      change (ι.mapMatrix J.form).det ≠ 0
      rw [← RingHom.map_det]
      exact (map_ne_zero ι).mpr J.form_nondegenerate))).toLinearEquiv.trans
        (dotProductEquiv K (Fin 3))

private theorem gramDualCoordinates_apply (J : HermitianForm 3 F) (ι : F →+* K)
    (v w : Fin 3 → K) :
    gramDualCoordinates J ι v w = v ⬝ᵥ ((J.form.map ι).mulVec w) := by
  change ((J.form.map ι).transpose.mulVec v) ⬝ᵥ w = _
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

/-- The Gram matrix intertwines the conjugate natural representation with
its genuine linear dual, over every coefficient embedding. -/
def naturalConjugateDualEquiv (J : HermitianForm 3 F) (ι : F →+* K) :
    (natural J (ι.comp J.conj.toRingHom)).Equiv (natural J ι).dual :=
  .mk (gramDualCoordinates J ι) (by
    intro g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change gramDualCoordinates J ι
      ((g.val.val.map (ι.comp J.conj.toRingHom)).mulVec v) w =
      gramDualCoordinates J ι v ((g⁻¹).val.val.map ι |>.mulVec w)
    rw [gramDualCoordinates_apply, gramDualCoordinates_apply,
      dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hJ := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
    have hi : g.val.val * (g⁻¹).val.val = 1 := by
      exact congrArg (fun x : J.specialSubgroup => x.val.val) (mul_inv_cancel g)
    have hm : J.conjTranspose g.val.val * J.form = J.form * (g⁻¹).val.val := by
      have h := congrArg (fun A => A * (g⁻¹).val.val) hJ
      simpa only [Matrix.mul_assoc, hi, Matrix.mul_one] using h
    have hm' := congrArg (fun A => A.map ι) hm
    simp only [Matrix.map_mul] at hm'
    have hct : (J.conjTranspose g.val.val).map ι =
        (g.val.val.map (ι.comp J.conj.toRingHom)).transpose := rfl
    rw [hct] at hm'
    rw [hm'])

variable [CharP K 2] [IsAlgClosed K]
/-- At the unitary field exponent, coefficient Frobenius has the dual character.
The proof uses the original Hermitian matrix, without choosing a standard form. -/
theorem natural_character_unitary_frobenius (J : HermitianForm 3 F)
    (ι : F →+* K) (s : ℕ) (hc : ∀ x, J.conj x = x ^ (2 ^ s))
    (g : J.specialSubgroup) :
    (natural J ι).character g ^ (2 ^ s) = (natural J ι).dual.character g := by
  have hcoeff := factorRep_character_comp (iterateFrobeniusEquiv K 2 s) ι
    Factor.natural (specialLinearInclusion J g)
  have hem : (iterateFrobeniusEquiv K 2 s : K →+* K).comp ι =
      ι.comp J.conj.toRingHom := by
    ext x
    change (ι x) ^ (2 ^ s) = ι (J.conj x)
    rw [hc, map_pow]
  rw [hem] at hcoeff
  have hdual := congrFun (char_iso (naturalConjugateDualEquiv J ι)) g
  exact hcoeff.symm.trans hdual

/-- Coefficient Frobenius at the unitary exponent exchanges the two
fundamental factors and fixes the trivial and trace-zero adjoint factors. -/
theorem factor_character_unitary_frobenius (J : HermitianForm 3 F)
    (ι : F →+* K) (s : ℕ) (hc : ∀ x, J.conj x = x ^ (2 ^ s))
    (a : Factor) (g : J.specialSubgroup) :
    (factorRep ι a).character (specialLinearInclusion J g) ^ (2 ^ s) =
      (factorRep ι (dualFactor a)).character (specialLinearInclusion J g) := by
  have hn (x : J.specialSubgroup) :
      (Representation.SL3.BinaryDefiningFactors.natural ι).character
        (specialLinearInclusion J x) ^ (2 ^ s) =
      (Representation.SL3.BinaryDefiningFactors.natural ι).character
        (specialLinearInclusion J x)⁻¹ := by
    have h := natural_character_unitary_frobenius J ι s hc x
    rw [Representation.char_dual] at h
    simpa only [natural, Representation.character, MonoidHom.comp_apply, map_inv] using h
  cases a with
  | trivial =>
      change (LinearMap.trace K K 1) ^ (2 ^ s) = LinearMap.trace K K 1
      simp
  | natural =>
      change (Representation.SL3.BinaryDefiningFactors.natural ι).character
        (specialLinearInclusion J g) ^ (2 ^ s) =
        (Representation.SL3.BinaryDefiningFactors.natural ι).dual.character
          (specialLinearInclusion J g)
      rw [Representation.char_dual]
      exact hn g
  | dual =>
      change (Representation.SL3.BinaryDefiningFactors.natural ι).dual.character
        (specialLinearInclusion J g) ^ (2 ^ s) =
        (Representation.SL3.BinaryDefiningFactors.natural ι).character
          (specialLinearInclusion J g)
      rw [Representation.char_dual]
      simpa only [map_inv, inv_inv] using hn g⁻¹
  | adjoint =>
      open TensorSimplicity.CharacterSeparation in
      have hn (x : J.specialSubgroup) :
          ι (Matrix.trace (specialLinearInclusion J x).val) ^ (2 ^ s) =
            ι (Matrix.trace (specialLinearInclusion J x⁻¹).val) := by
        simpa only [natural_character_trace, ← map_inv] using hn x
      change (iterateFrobeniusEquiv K 2 s)
        ((factorRep ι .adjoint).character (specialLinearInclusion J g)) =
          (factorRep ι .adjoint).character (specialLinearInclusion J g)
      rw [← factorRep_character_comp,
        TensorSimplicity.CharacterSeparation.adjoint_character,
        TensorSimplicity.CharacterSeparation.adjoint_character]
      change 1 + (ι (Matrix.trace (specialLinearInclusion J g).val)) ^ (2 ^ s) *
        (ι (Matrix.trace (specialLinearInclusion J g)⁻¹.val)) ^ (2 ^ s) = _
      rw [← map_inv, hn g, hn g⁻¹, inv_inv, map_inv]
      ring

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
