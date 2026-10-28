module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.Construction

/-!
# The full SU₃ embedding in the split-octonion G₂ model

This module preserves the original existence interface. The actual faithful
homomorphism and its algebra comparison are reexported from `Construction`.
Combined torus consumers import `Construction` directly: the independent
`UnitaryRealization` module also has an `exists_unitary_embedding` theorem,
for the different map from field units into SU₃.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1. The full SU₃ is used, with no projective quotient.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus

variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The second geometric input of the twisted cubic torus construction,
with every algebra comparison and descent premise discharged. -/
theorem exists_unitary_embedding (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ ι : (standardForm F p).specialSubgroup →* Model F, Function.Injective ι :=
  exists_unitary_model_embedding F p hF hp

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
