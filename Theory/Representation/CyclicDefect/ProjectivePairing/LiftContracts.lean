module

public import Theory.Representation.CyclicDefect.RealLine
public import Theory.Representation.CoefficientReduction
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Actual lifting data for projective Brauer reciprocity

An integral lift consists of a projective group-algebra module over a local
coefficient ring, an injective complex embedding, a residue map, and an actual
intertwining equivalence with the given modular representation. The chosen
root must agree with both roots of the cyclic correspondence. In particular,
ordinary lattices alone do not supply this data.

The separate ordinary comparison records the two character conclusions used
in Feit's IV.3.3: equality on regular elements and vanishing on singular
elements. These suffice for nonnegative integrality by ordinary averaging.
Neither structure has an existence instance. Their construction requires the projective lifting
and character comparison results of Feit I.16–17 and IV.2, respectively.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ}

/-- A genuine integral projective lift, with both coefficient maps and the
root correspondence specified. No character or scalar-product conclusion is
part of this input. -/
structure IntegralLift (L : CyclicRootLift K m) (Q : Representation K G V) where
  Coeff : Type
  [coeffRing : CommRing Coeff]
  [coeffLocal : IsLocalRing Coeff]
  complex : Coeff →+* ℂ
  complex_injective : Function.Injective complex
  residue : Coeff →+* K
  residue_ker : RingHom.ker residue = IsLocalRing.maximalIdeal Coeff
  degree : ℕ
  rep : Representation Coeff G (Fin degree → Coeff)
  projective : Module.Projective (MonoidAlgebra Coeff G) rep.asModule
  reduction : (Representation.mapCoefficients residue rep).Equiv Q
  root : Coeff
  root_pow : root ^ m = 1
  root_complex : complex root = L.complexRoot
  root_residue : residue root = L.modularRoot

/-- The ordinary representation and the two independent comparison facts
needed for character averaging. Existence is a separate theorem. -/
structure OrdinaryModel (p : ℕ) (L : CyclicRootLift K m) (Q : Representation K G V) where
  degree : ℕ
  rep : Representation ℂ G (Fin degree → ℂ)
  regular_eq : ∀ g, ¬ p ∣ orderOf g → rep.character g = L.value Q g
  singular_zero : ∀ g, p ∣ orderOf g → rep.character g = 0

end Representation.CyclicDefect.ProjectivePairing
