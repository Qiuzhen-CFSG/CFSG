module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Arithmetic
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Weyl

/-!
# Split inputs for the third cyclotomic torus

This module specifies the two independent geometric inputs to descent:
a faithfully embedded primary plane fixed by the inner twist of graph-field,
and a Lang equation for the concrete twisting word. `TwistedPlane` is an
input contract, not an assertion that such a plane exists. Its constructor
must use the original coroot torus in the split group.

Source: GLS3 §2.2 (graph-field fixed points), §6.1 (central coverings).
-/

@[expose] public section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
open Triality.Standard

instance primaryOrder_neZero (n p : ℕ) : NeZero (primaryOrder n p) :=
  ⟨Nat.ne_of_gt (primaryOrder_pos n p)⟩

/-- The entire primary plane; its exponent need not be prime. -/
abbrev Plane (n p : ℕ) := Multiplicative (ZMod (primaryOrder n p) × ZMod (primaryOrder n p))

def leftVector (n p : ℕ) : Plane n p := Multiplicative.ofAdd (1, 0)
def rightVector (n p : ℕ) : Plane n p := Multiplicative.ofAdd (0, 1)

/-- Literal split-group data needed before Lang conjugation. -/
structure TwistedPlane (n : ℕ) (hn : 0 < n) (p : ℕ) where
  embedding : Plane n p →* SplitGroup (binaryParameters n hn)
  injective : Function.Injective embedding
  twisted_fixed : ∀ z, twistWord n hn *
    graphFieldAutomorphism (binaryParameters n hn) (embedding z) =
      embedding z * twistWord n hn
  conjugate_left : twistWord n hn * embedding (leftVector n p) * (twistWord n hn)⁻¹ =
    embedding (leftVector n p) ^ (2 ^ n) ^ 2
  conjugate_right : twistWord n hn * embedding (rightVector n p) * (twistWord n hn)⁻¹ =
    embedding (rightVector n p)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
