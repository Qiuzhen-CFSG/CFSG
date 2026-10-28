module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Factorization
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Separation

/-!
# Concrete geometry of the relative Ree Weyl quotient

This module exports the three matrix facts needed by the existing quotient
reductions, for every coefficient field (and hence for `1 ≤ m`):

* `borel_inf_normalizerWords_normal_of_kernel` proves normality of the
  Borel–normalizer intersection inside the specified normalizer subgroup;
* `normalizerWords_le_fixedTorus_sup_weylSubgroup_of_monomial` expresses every
  fixed normalizer word using the fixed torus and the two actual orbit lifts;
* `weylLift_linear_inv_mul_suzuki_not_mem_borel` separates those two lifts.

Normality uses the triangular-kernel hypothesis. Generation additionally uses
the genuine Weyl-monomial presentation of every split normalizer word. The
separation calculation is unconditional. The proofs retain the torus factors,
extend the integral Tits-word comparison to the present coefficient field,
and prove fixed-point descent before invoking Weyl-length descent.

These are conditional geometric inputs to the source-theorem assembly, which
must discharge the two shared matrix hypotheses. Quotient generation and
distinctness of quotient classes remain the existing `QuotientCalculations`
reductions; this module assumes no BN-pair or requested conclusion.

Source: GLS3 2.3.2–4, `refs/KGroup/GLS3/chapter2.tex`.
-/
