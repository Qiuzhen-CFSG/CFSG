module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TwistedKernels.Lattice

/-!+# D4 reflection factorizations supported on a displacement lattice

The integral coordinates of a root are its pairings with the four marked
simple coroots. A doubled-root factorization of `w` expresses it as a product
of actual D4 root reflections, each with twice its root weight in `(w - 1)X`.
This is a finite lattice problem, independent of torus points and normalizer
lifts. In characteristic two, evaluation at a point fixed by `w` makes every
such root character one, because squaring is injective in the field.

No existence of these factorizations is asserted by this module. Their
character-theoretic consequence is proved in `Normalizer.Stabilizer`.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 4.2, 5.3, 6.4(b),
and the reflection generation in 8.2(6)--(7), specialized to D4.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
namespace ConnectedCentralizer.Normalizer.Stabilizer

/-- An actual D4 root in integral simple-coroot coordinates. -/
def rootWeight (r : TypeDRootIndex 4) : Weight := fun i =>
  (typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 i)

/-- A reflection word with integral displacement witnesses for twice each
root weight. Both the word and its weights use the specified D4 pairing. -/
def DoubledRootFactorization (ρ : AmbientCount.WeightRepresentation)
    (w : AmbientCount.Weyl) : Prop :=
  ∃ l : List (TypeDRootIndex 4),
    (l.map (RootPairing.weylGroup.ofIdx (typeDRootPairing 2))).prod = w ∧
      ∀ r ∈ l, ∃ a : Weight, ρ w a - a = (2 : ℤ) • rootWeight r

end ConnectedCentralizer.Normalizer.Stabilizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
