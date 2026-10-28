module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients

/-!
# Simple Weyl conjugation on all canonical D₄ root curves

The positive coefficient comparison extends to negative roots along their
actual negative-simple Tits routes. Full-lattice covariance then identifies
all canonical integral divided powers with the binary coefficient matrices.
Specialization to a characteristic-two ring removes the integral signs, and
identifies the actual Weyl word with the specialized Tits lift. This proves
parameter-preserving conjugation on all 24 roots, including over GF(8).

Source: GLS3 2.3.8(b), 2.4.8(e), and the common integral Chevalley lattice
(`refs/KGroup/GLS3/chapter2.tex`). No Weyl-group identification is assumed.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.ConcreteBruhat.RootConjugation
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b
local instance : InvolutiveNeg (TypeDRootIndex 4) := (typeDRootPairing 2).indexNeg

private lemma enumeration_negative (r : Fin 24) :
    rootEnumeration (negativeIndex r) = -rootEnumeration r := by
  apply (typeDRootPairing 2).root_eq_neg_iff.mp
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_neg, Pi.neg_apply, rootCoords_spec]
  rw [rootCoords_negativeIndex]
  simp

private lemma word_covariance
    (word : List (typeDRootPairing_base 2).support) (r : Fin 24) (d : Fin 4) :
    binarySpecialization (titsWord word) * dividedCoefficient r d =
      dividedCoefficient
        (rootEnumeration.symm (reflectionWord word (rootEnumeration r))) d *
      binarySpecialization (titsWord word) := by
  induction word with
  | nil => simp [titsWord, reflectionWord, binarySpecialization_one]
  | cons j word ih =>
      obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
      simp only [titsWord, binarySpecialization_mul, binarySpecialization_titsLift]
      rw [mul_assoc, ih, ← mul_assoc, binaryTits_divided, mul_assoc]
      apply congrArg (fun s => dividedCoefficient s d *
        (binaryTits i * binarySpecialization (titsWord word)))
      apply rootEnumeration.injective
      simp only [rootEnumeration_reflectionTable, Equiv.apply_symm_apply,
        reflectionWord, typeDRootPairing_baseEquiv_val]

/-- The canonical divided powers for every root agree with the binary matrices. -/
theorem canonicalCoefficient_all (r : TypeDRootIndex 4) (d : Fin 4) :
    binarySpecialization (rootDividedPower (b := typeDRootPairing_base 2) r d) =
      dividedCoefficient (rootEnumeration.symm r) d := by
  by_cases hr : (typeDRootPairing_base 2).IsPos r
  · obtain ⟨i, rfl⟩ : r ∈ Set.range rootIndex := by rw [range_rootIndex]; exact hr
    change canonicalCoefficient i d = _
    rw [canonicalCoefficient_eq, ← rootEnumeration_positiveIndex, Equiv.symm_apply_apply]
  · simp only [rootDividedPower, dif_neg hr, transportedMatrix,
      binarySpecialization_mul]
    obtain ⟨j, hj⟩ := (typeDRootPairing_baseEquiv 2).surjective
      (rootRoute (b := typeDRootPairing_base 2) (-r)).simple
    have hf : binarySpecialization
        (fDividedPower (rootRoute (b := typeDRootPairing_base 2) (-r)).simple d) =
        dividedCoefficient (negativeIndex (simpleIndex j)) d := by
      rw [← hj]
      exact fDividedPower_binary j d
    rw [hf, word_covariance, mul_assoc, ← binarySpecialization_mul,
      titsWord_mul_inv, binarySpecialization_one, mul_one]
    apply congrArg (fun s => dividedCoefficient s d)
    apply rootEnumeration.injective
    simp only [Equiv.apply_symm_apply, enumeration_negative, rootEnumeration_simpleIndex]
    rw [reflectionWord_neg]
    rw [← typeDRootPairing_baseEquiv_val, hj,
      (rootRoute (b := typeDRootPairing_base 2) (-r)).target]
    exact neg_neg r


/-- The canonical integral root curve on the full enumerated Geck lattice. -/
theorem rootCurveUnit_matrix {F : Type*} [CommRing F] [CharP F 2]
    (r : TypeDRootIndex 4) (t : F) :
    Matrix.reindexRingEquiv F latticeEnumeration.symm
      (rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t).val =
      matrixCurve (rootEnumeration.symm r) t := by
  have hc (d : Fin 4) :
      Matrix.reindexRingEquiv F latticeEnumeration.symm
        (specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) r d)) =
      (scalarMap F).mapMatrix (dividedCoefficient (rootEnumeration.symm r) d) := by
    rw [← canonicalCoefficient_all r d]
    ext a b
    exact (map_intCast (scalarMap F) _).symm
  change Matrix.reindexRingEquiv _ latticeEnumeration.symm
    (1 + t • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) r 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) r 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2) r 3)) = _
  have hr (s : F) (M : Matrix LatticeIndex LatticeIndex F) :
      Matrix.reindexRingEquiv _ latticeEnumeration.symm (s • M) =
        s • Matrix.reindexRingEquiv _ latticeEnumeration.symm M := rfl
  simp only [map_add, map_one, hr]
  rw [hc ⟨1, by decide⟩, hc ⟨2, by decide⟩, hc ⟨3, by decide⟩]
  simp [dividedCoefficient, matrixCurve]

private lemma tits_curve {F : Type*} [CommRing F] [CharP F 2]
    (i : Fin 4) (r : Fin 24) (t : F) :
    (scalarMap F).mapMatrix (binaryTits i) * matrixCurve r t =
      matrixCurve (reflectionTable i r) t * (scalarMap F).mapMatrix (binaryTits i) := by
  have h1 := congrArg (scalarMap F).mapMatrix (binaryTits_divided i r 1)
  have h2 := congrArg (scalarMap F).mapMatrix (binaryTits_divided i r 2)
  simp only [map_mul] at h1 h2
  change (scalarMap F).mapMatrix (binaryTits i) * (scalarMap F).mapMatrix (linearCoefficient r) =
    (scalarMap F).mapMatrix (linearCoefficient (reflectionTable i r)) *
      (scalarMap F).mapMatrix (binaryTits i) at h1
  change (scalarMap F).mapMatrix (binaryTits i) * (scalarMap F).mapMatrix (quadraticCoefficient r) =
    (scalarMap F).mapMatrix (quadraticCoefficient (reflectionTable i r)) *
      (scalarMap F).mapMatrix (binaryTits i) at h2
  simp only [matrixCurve, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, one_mul]
  rw [h1, h2]

open Parabolics
/-- The actual simple Weyl word is the characteristic-two Tits matrix. -/
theorem weylWord_matrix (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    let := rankOneExtensionCharTwo P hp
    Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm
      (weylWord P i 1).val.val =
      (scalarMap (ExtensionField P)).mapMatrix (binaryTits i) := by
  let := rankOneExtensionCharTwo P hp
  have hw : (weylWord P i 1).val =
      rootCurveTitsWord (S := ExtensionField P) [typeDRootPairing_baseEquiv 2 i] := by
    rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
    simp only [weylWord, positiveRoot, negativeRoot, Subgroup.coe_mul,
      RootPairing.SimpleGeckGroup.positive, RootPairing.SimpleGeckGroup.negative, inv_one]
  rw [hw, ← binarySpecialization_titsLift]
  change Matrix.reindexRingEquiv _ latticeEnumeration.symm
    (specializeMatrix (titsLift _ * 1)) = _
  rw [mul_one]
  ext a b
  exact (map_intCast (scalarMap (ExtensionField P)) _).symm

/-- Intertwining on all canonical root curves in the ambient matrix units. -/
theorem weylWord_rootCurveUnit_intertwine (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    (weylWord P i 1).val *
        rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t =
      rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
        (rootReflection i r) t * (weylWord P i 1).val := by
  let := rankOneExtensionCharTwo P hp
  apply Units.ext
  apply (Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm).injective
  change Matrix.reindexRingEquiv _ latticeEnumeration.symm (_ * _) =
    Matrix.reindexRingEquiv _ latticeEnumeration.symm (_ * _)
  simp only [map_mul, rootCurveUnit_matrix, weylWord_matrix P hp]
  obtain ⟨r, rfl⟩ := rootEnumeration.surjective r
  rw [rootReflection, ← rootEnumeration_reflectionTable,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact tits_curve i r t

/-- Simple Weyl conjugation preserves the parameter on every canonical root curve. -/
theorem weylWord_rootCurveUnit_conjugation (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    (weylWord P i 1).val *
        rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r t *
        (weylWord P i 1).val⁻¹ =
      rootCurveUnit (integralChevalleyRootOperators (b := typeDRootPairing_base 2))
        (rootReflection i r) t := by
  rw [weylWord_rootCurveUnit_intertwine P hp, mul_inv_cancel_right]

end
end Triality.Standard.ConcreteBruhat.RootConjugation
