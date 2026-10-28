module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.nonsingular_coefficient
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceSetup

/-!
This module exports nonsingularity of expected Chevalley coefficients for the
`RelativeRootRepresentationSource` contract.  The source stores a rational
root pairing, its Dynkin classification, and the root-system realization of
the ambient root datum; the generic connected-or-diagonal Dynkin argument is
provided by `nonsingular_coefficient` and is applied here without introducing
an irreducible-root-system instance.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem RelativeRootRepresentationSource.expectedChevalleyCoefficient_ne_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (hNonsingular : ¬ IsUSingular S.classification (ringChar k))
    {α β : S.D.Root} {q : ChevalleyCommutatorTerm S.D.Root} {c : k}
    (h : HasExpectedChevalleyCoefficient S.D S.pairing
      (Equiv.refl S.D.Root) α β q c) :
    c ≠ 0 := by
  exact h.ne_zero_of_nonsingular_of_hasDynkinType_or_diagonal
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.isRealization
      S.rootSystemRealization S.classification S.dynkinType hNonsingular

end Theory.AlgebraicGroup
