module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.SourceBinary
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Exhaustion
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Source

/-!
# Actual Ree involution bounds from the proved finite tensor family

Finite irreducibility, factor distinction and exhaustion now supply all module
classification clauses in the intrinsic binary bound. The proved action and
center transport then give the same bound for the literal quasisimple cover.
Only the actual odd-order class count and the universal semisimple-center
source theorem remain; no fixed-space or representation certificate is assumed.

This serves both the original B.4.2 action and B.1 component recognition.
Source: Guralnick–Malle II, Lemma 8.8; Steinberg (1963), 3.9 and 12.2.
-/

public section
open Theory.AlgebraicGroup Representation
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate
universe u v

variable {m : ℕ}
  (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
      ∀ T : ClosedSubgroup H, IsMaximalTorus T →
        Subgroup.center (Variety.Point H) ≤ T.toSubgroup)
  (hclasses : Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤
    Nat.card (Classification.Steinberg.RestrictedWeight m))

include hcenters hclasses

/-- The original binary model involution bound with all finite module clauses proved. -/
theorem binaryModelInvolutionBound_of_class_bound_and_semisimple_centers (hm : 1 ≤ m) :
    BinaryModelInvolutionBound.{v} m := by
  apply binaryModelInvolutionBound_of_finite_tensor_classification hm
  · intro F _ _ _ B hB
    exact Classification.Steinberg.FiniteRootAction.exceptionalTensor_irreducible m B
      (Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
        (hcenters F)) hB (Classification.coefficientHom F m)
  · intro F _ _ _ B C hB hC he
    exact Classification.Steinberg.FiniteRootAction.exceptionalTensor_distinction m
      (Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
        (hcenters F)) B C hB hC he
  · intro F W _ _ _ _ _ _ σ hσ
    let := hσ
    have hU := Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
      (hcenters F)
    exact Classification.Steinberg.FiniteRootAction.exists_tensor_of_class_bound m hU
      (Classification.coefficientHom F m)
      (Classification.Steinberg.FiniteRootAction.exceptionalTensor_distinction m hU)
      hclasses σ

/-- The literal quasisimple-cover involution bound, including the original action. -/
theorem coverInvolutionBound_of_class_bound_and_semisimple_centers (hm : 1 ≤ m) :
    CoverInvolutionBound.{u,v} m :=
  coverInvolutionBound_of_binary_source hm
    (binaryModelInvolutionBound_of_class_bound_and_semisimple_centers hcenters hclasses hm)

end ReeF4.FixedSpaceEstimate
