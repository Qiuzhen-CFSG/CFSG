module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The marked plane-pair subgroup needed for odd symplectic covers

The stabilizer of an unordered orthogonal decomposition of symplectic
four-space into two nondegenerate planes is a copy of SL₂(p) wreath C₂.
Its index is odd. The element interchanging the two planes is conjugate
in Sp₄(p) to the element acting as minus one on just one plane.

This module specifies the concrete embedding and fusion data consumed by
the central-cover argument. It does not assert that these data have been
constructed. In particular, the ambient carrier is the actual matrix group,
and the index and conjugacy assertions refer to the displayed embedding.

Source: the odd type C₂ multiplier calculation behind GLS3 §6.1 and
Aschbacher–Smith I.1.1–4, printed pp.407–408, for the family in A.2.2(2).
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary

/-- The actual rank-one matrix group on a symplectic plane. -/
abbrev Plane (p : ℕ) [Fact p.Prime] := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

/-- Marked geometric input, with an actual embedding, actual odd index, and
actual ambient conjugacy. Its construction is a separate obligation. -/
structure PlaneModel (p : ℕ) [Fact p.Prime] where
  action : Multiplicative (ZMod 2) →* MulAut (Plane p × Plane p)
  action_generator : action (.ofAdd 1) = MulEquiv.prodComm
  inclusion : (Plane p × Plane p) ⋊[action] Multiplicative (ZMod 2) →* Sp (ZMod p)
  injective : Function.Injective inclusion
  odd_index : Odd inclusion.range.index
  swap_conjugate : IsConj (inclusion (SemidirectProduct.inl (-1, 1)))
    (inclusion (SemidirectProduct.inr (.ofAdd 1)))

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
