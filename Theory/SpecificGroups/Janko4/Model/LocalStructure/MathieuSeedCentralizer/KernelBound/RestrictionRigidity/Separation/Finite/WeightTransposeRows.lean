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


theorem weightTransposeRows_check : ∀ (k : Fin 44) (r : Fin 56), (weightTransposes.get k).get r =
      xorList (List.ofFn (fun j : Fin 56 => if ((halfRows (weights.get k.castSucc)).get j).testBit r.val
        then 2^j.val else 0)) := by
    simp only [halfRows, get_ofFn]
    decide +kernel

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
