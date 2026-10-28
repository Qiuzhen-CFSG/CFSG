module
public import Theory.Representation.Suzuki.SmallDegree.Classification.SimpleDistinct
public import Theory.Representation.AbsolutelyIrreducible
/-!
# Absolute irreducibility of the concrete Suzuki tensors

Iterated scalar extension and the proved tensor irreducibility over every
coefficient field give the scalar endomorphism property used for the actual
Steinberg multiplicity action in Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open SuzukiNatural

/-- Every concrete tensor is absolutely irreducible over each coefficient extension. -/
theorem tensorRep_absolutelyIrreducible (m : ℕ) (hm : 1 ≤ m)
    (K : Type*) [Field K] [Algebra (F m) K] (I : Support m) :
    IsAbsolutelyIrreducible (tensorRep m K I) := by
  constructor
  change IsIrreducible (extendScalars (AlgebraicClosure K)
    (extendScalars K (wordRep m (exponents I))))
  rw [RepEquiv.irreducible_euqiv (extendScalars_comp K (wordRep m (exponents I)))]
  exact tensorRep_irreducible hm I
end Representation.SuzukiSmallDegree
