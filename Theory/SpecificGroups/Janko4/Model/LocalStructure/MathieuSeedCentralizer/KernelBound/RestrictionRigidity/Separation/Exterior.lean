module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks00
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks05
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks15
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks20
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks25
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks30
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks35
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior.Checks40

/-!
# Annihilation of the complete restriction space

The first 44 published weights are transported through the exact adapted
embedding. Their transported duals vanish on all 1221 original exterior
generators; linearity then proves vanishing on the complete restriction space.
No dimension or selected-basis completeness claim is used.

Source: KernelBound/source/README.md and Separation/source/README.md, describing
the kernel-restriction.json calculation on the published ATLAS matrices.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

theorem exterior_checks (k : Fin 44) :
    flatMatrix (duals.get k.castSucc) = embedding * decodeHalf (weights.get k.castSucc) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get k.castSucc) (basisFlat i.val) = false := by
  by_cases h0 : k.val < 5
  · exact exterior_checks_0 k.val (by omega) h0 (by omega)
  by_cases h5 : k.val < 10
  · exact exterior_checks_5 k.val (by omega) h5 (by omega)
  by_cases h10 : k.val < 15
  · exact exterior_checks_10 k.val (by omega) h10 (by omega)
  by_cases h15 : k.val < 20
  · exact exterior_checks_15 k.val (by omega) h15 (by omega)
  by_cases h20 : k.val < 25
  · exact exterior_checks_20 k.val (by omega) h20 (by omega)
  by_cases h25 : k.val < 30
  · exact exterior_checks_25 k.val (by omega) h25 (by omega)
  by_cases h30 : k.val < 35
  · exact exterior_checks_30 k.val (by omega) h30 (by omega)
  by_cases h35 : k.val < 40
  · exact exterior_checks_35 k.val (by omega) h35 (by omega)
  exact exterior_checks_40 k.val (by omega) k.isLt (by omega)

/-- Each of the first 44 separating functionals vanishes on every restriction
of a form in the complete original exterior space. -/
theorem restriction_annihilated (k : Fin 44) {R : HalfMatrix} (hR : R ∈ restrictionSpace) :
    functional (weights.get k.castSucc) R = 0 :=
  functional_restriction_zero_of_dual _ _ (exterior_checks k).1 (exterior_checks k).2 hR

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
