/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianModuloTwoQuotient.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# IcosianModuloTwoQuotient

The quotient of the integral order by twice the order is M₂(F₄).
The proved kernel description identifies the two-sided ideal, and the
surjective reduction map induces the ring equivalence.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianModuloTwoQuotient.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra

/-- The two-sided ideal whose elements are exactly twice icosians. -/
def icosianTwiceIdeal : Ideal icosianOrder := RingHom.ker icosianModuloTwo

instance icosianTwiceIdeal_twoSided : icosianTwiceIdeal.IsTwoSided := inferInstanceAs
  (RingHom.ker icosianModuloTwo).IsTwoSided

theorem icosianTwiceIdeal_mem (x : icosianOrder) :
    x ∈ icosianTwiceIdeal ↔ ∃ y : icosianOrder,x=2*y :=
  icosianModuloTwo_eq_zero_iff_two_mul x

/-- The actual scalar ring quotient by twice the order is the full two-by-two matrix ring. -/
def icosianModuloTwoQuotient : icosianOrder ⧸ icosianTwiceIdeal ≃+* IcosianMatrix :=
  RingHom.quotientKerEquivOfSurjective icosianModuloTwo_surjective

theorem icosianModuloTwoQuotient_mk (x : icosianOrder) :
    icosianModuloTwoQuotient (Ideal.Quotient.mk _ x)=icosianModuloTwo x := rfl

end Atlas.Algebra
