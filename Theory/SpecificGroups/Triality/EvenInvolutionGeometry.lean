module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.Coefficients
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.OddExponent
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.Residual

/-!
# Root elements and coefficient detection for binary triality

The genuine pinned graph-field carrier has faithful long- and short-root
parametrizations over GF(2ⁿ) and GF(2³ⁿ). Nonzero parameters give involutions
in its root-defined positive subgroup. The short curve detects the full cubic
coefficient action. At odd exponent, all two-power automorphisms admitting
an inner–coefficient expression are inner; a non-inner such automorphism
therefore forces n = 2m with m > 0. These statements include n = 1.

The residual transfer preserves the actual embeddings of O²(C(r)) and
O²(C_Q(r)) once C(r) ≤ Q is proved. Classification of every involution into
the two root classes, proper root-parabolic centralizer containment, and the
mixed inner–coefficient Sylow-fixer calculation remain separate obligations.
Consequently this module does not yet assert the full triality cases of
Aschbacher–Smith 16.1.4(1) or 16.1.6 (printed pp.1171–1172), nor the root
geometry used in 16.5.13–14 (pp.1201–1203), in `refs/quasithin.pdf`.
-/
