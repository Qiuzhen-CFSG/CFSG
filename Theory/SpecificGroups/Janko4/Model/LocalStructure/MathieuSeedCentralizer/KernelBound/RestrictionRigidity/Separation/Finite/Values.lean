module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.RowChecks

/-!
# Finite evaluations and pair coverage

Every displayed matrix identity is checked using ordinary kernel reduction.

Source: KernelBound/source/README.md and kernel-restriction.json. Numerical
witnesses are checked by Lean; the generator is not trusted.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

set_option maxRecDepth 10000
set_option Elab.async false
attribute [local irreducible] symWeights weights linearWords productWords productPairs survivor
  alternativeBasisWords squareBasis topOperator testForm weightTransposes


 theorem linear_values : ∀ (k : Fin 44) (i : Fin 45),
    halfDot (weights.get k.castSucc) (linearWords.get i) =
      if i.val < 44 then (if i.val = k.val then 1 else 0) else bit survivor k.val := by decide +kernel

 theorem quadratic_values : ∀ (k : Fin 44) (p : Fin 1035),
    halfDot (if (productPairs.get p).1 = (productPairs.get p).2 then weights.get k.castSucc
      else symWeights.get k) (productWords.get p) = 0 := by decide +kernel


end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
