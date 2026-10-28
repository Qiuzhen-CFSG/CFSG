module
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.CorootTorus
public import Theory.AlgebraicGroup.RootSystems.F4RootLattice
import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootPlanePresentation.CorootMatrices

/-!
# Matrix interface for the parameter-one sign torus

This bridge reuses the actual simple-coroot matrix identity and the faithful
F4 diagonal parameters. The root-plane implementation is a private import:
its generated local instance names collide with the root-transport branch.
Only the lower-level matrix interface is exported, preserving both branches.
No faithfulness assertion about either completion is used.

Source: Steinberg, Lectures on Chevalley Groups, §3, Lemma 28 and Theorem 8;
GLS3 Theorem 2.9.3, normalizer argument, chapter2.tex lines 1429–1441.
-/

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.SignTorusMatrices
public local instance signRootsFintype : Fintype typeF4Roots := Fintype.ofFinite _
/-- The actual six-letter simple-coroot word, over every field. -/
public theorem coroot (F : Type*) [Field F] (i : typeF4RootPairing_base.support) (t : Fˣ) :
    matrixH (b := typeF4RootPairing_base) (F := F) i t =
      integralChevalleyTorusElement (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter i t⁻¹) := rootPlane_matrixH_simple i t

/-- The literal diagonal parameter homomorphism, in the coroot-word convention. -/
@[expose] public def parameterMatrixHom (F : Type*) [Field F] : (Fin 4 → Fˣ) →*
    (Matrix (typeF4RootPairing_base.support ⊕ typeF4Roots)
      (typeF4RootPairing_base.support ⊕ typeF4Roots) F)ˣ where
  toFun u := integralChevalleyTorusElement (P := typeF4RootPairing)
    (fun q => (u (typeF4RootPairing_baseEquiv.symm q))⁻¹)
  map_one' := integralChevalleyTorusElement_one
  map_mul' u v := by
    rw [← integralChevalleyTorusElement_mul]
    congr 1
    funext q
    simp only [Pi.mul_apply, mul_inv_rev]
    exact mul_comm _ _

/-- F4 root-lattice equality detects every parameter of this diagonal. -/
public theorem parameterMatrixHom_injective (F : Type*) [Field F] :
    Function.Injective (parameterMatrixHom F) := rootTorusMatrixHom_injective F

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.SignTorusMatrices
