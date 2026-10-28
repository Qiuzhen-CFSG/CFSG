module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.CommonSimpleRigidity.NormalizerLength
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Reduction

/-!
# Ordinary vertices and normalizer lengths

This contract states the earlier-source length theorem needed in the proof
of Feit VII.2.25. It uses actual nonprojective summands of the restriction
to the normalizer. Membership in the literal reduced principal block is
retained, and reduction is always at the given `CompatibleRoots.residue`.
There is no existence instance and no uniqueness conclusion in the contract.

Source: Feit VII.2.9, VII.2.14 and VII.2.19, as used on printed p.304.
-/

public section
namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {p m : ℕ} {K G : Type*} [Field K] [Group G] [Finite G]
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}

/-- The ordinary vertex fixes the normalizer length of every indecomposable
reduction at the given residue map. The principal block action is explicit. -/
@[expose] def VertexNormalizerLengths (r : CompatibleRoots d K m)
    (P : Sylow p G) (v : {i // i ∈ d.block}) : Prop :=
  ∃ l : ℕ, (l = 1 ∨ l = p - 1) ∧
    ∀ X : OrdinaryLattice d v.val,
      Module.IsIndecomposable (MonoidAlgebra K G) (X.reduction r).asModule →
        (X.reduction r).asAlgebraHom (ModuleTree.reducedPrincipal d r.residue) = 1 ∧
          HasNormalizerLength P (X.reduction r) l

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
