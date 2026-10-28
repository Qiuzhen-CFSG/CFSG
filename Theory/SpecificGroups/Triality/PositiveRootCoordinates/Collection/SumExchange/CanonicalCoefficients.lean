module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.SimpleCoefficients
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients.Covariance

/-!
# Canonical binary D₄ divided-power coefficients

The actual integral divided powers, specialized to `ZMod 2` and reindexed on
all 28 Geck coordinates, equal the concrete coefficient matrices for every
positive root and every degree used by the root curves.

The simple-root comparison starts an induction along an arbitrary Tits word.
Simple-reflection covariance supplies the induction step, and the inverse-word
identity cancels the conjugating matrices. Applying this to the chosen
`rootRoute` uses only its target equation: no explicit alternative word,
reduced-word comparison, or extra equivariance premise is assumed.

Source: the common-lattice Chevalley construction in GLS3 §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`). This comparison supplies the canonical
coefficient premise in the positive-root sum-exchange assembly.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.PositiveCoordinates.SumExchangeData
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private lemma binarySpecialization_titsWord_covariance
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

/-- Every canonical positive-root divided power agrees with its full-lattice
binary coefficient matrix. The proof works for the arbitrary chosen route. -/
theorem canonicalCoefficient_eq (i : Fin 12) (d : Fin 4) :
    canonicalCoefficient i d = dividedCoefficient (positiveIndex i) d := by
  unfold canonicalCoefficient
  rw [rootDividedPower_of_pos _ (rootIndex_positive i)]
  change binarySpecialization
    (transportedMatrix (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).word
      (eDividedPower (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple d)) = _
  unfold transportedMatrix
  rw [binarySpecialization_mul, binarySpecialization_mul]
  obtain ⟨j, hj⟩ := (typeDRootPairing_baseEquiv 2).surjective
    (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple
  have he : binarySpecialization
      (eDividedPower (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple d) =
      dividedCoefficient (simpleIndex j) d := by
    rw [← hj]
    exact eDividedPower_binary j d
  rw [he, binarySpecialization_titsWord_covariance, mul_assoc,
    ← binarySpecialization_mul, titsWord_mul_inv, binarySpecialization_one, mul_one]
  apply congrArg (fun r => dividedCoefficient r d)
  apply rootEnumeration.injective
  rw [Equiv.apply_symm_apply, rootEnumeration_simpleIndex, rootEnumeration_positiveIndex]
  change reflectionWord (b := typeDRootPairing_base 2) _
    (typeDRootPairing_baseEquiv 2 j) = rootIndex i
  rw [hj]
  exact (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).target

end
end Triality.Standard.PositiveCoordinates.SumExchangeData
