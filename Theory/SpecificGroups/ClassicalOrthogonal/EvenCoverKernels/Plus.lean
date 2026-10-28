module

public import Theory.SpecificGroups.ClassicalOrthogonal.EvenCoverKernels.Plus.PrimeReduction

/-!
# Higher split orthogonal covering-kernel reductions

The shared odd-prime exclusion contract and its reduction to the actual
universal kernel are re-exported here. Independent rank-four and rank-raising
proofs can import `Plus.PrimeReduction` while this module retains final assembly.
The concrete canonical Siegel lifts are constructed in `Plus.RootLifts`.

The current kernel and B.1.13 applications are conditional on those two missing
calculations. GLS3 Section 6.1, Tables 6.1.2–6.1.3 and Theorem 6.1.4 give the
source target: a two-group kernel, retaining the exceptional multiplier of D₄(2).
-/
