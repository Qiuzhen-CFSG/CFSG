module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftComparison.Singular.Inputs
public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftComparison.Singular.CyclicTrace

/-!
# Singular characters of integral projective lifts

The complex character of a supplied integral projective lift vanishes on
every element whose order is divisible by the residue characteristic.
Restricting to the element's cyclic subgroup gives exact integral trace
zero by `Singular.CyclicTrace`; mapping that equality along the complex
embedding gives the claimed character value. The cyclic proof uses integral
spectral projectors on a finite projective cover, so no additional locality
or freeness premise remains.

This is the singular-vanishing clause of Feit, *The Representation Theory
of Finite Groups*, IV.2.5 (printed p.144), used in IV.3.3 (pp.145–146).
The integral lift is supplied explicitly; its existence is a separate result.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing.IntegralLift

attribute [local instance] IntegralLift.coeffRing

variable {K G V : Type*} [Field K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] {m : ℕ} {L : CyclicRootLift K m}
  {Q : Representation K G V} (A : IntegralLift L Q)

/-- The ordinary character of an integral projective lift is zero at every
singular element. Vanishing holds over the coefficient ring before applying
the complex embedding. -/
theorem character_eq_zero_of_singular (p : ℕ) [Fact p.Prime] [CharP K p]
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (g : G) (hg : p ∣ orderOf g) :
    A.complexRep.character g = 0 := by
  rw [A.character_eq_map_cyclic_trace g, A.cyclic_trace_eq_zero p horder g hg, map_zero]

end Representation.CyclicDefect.ProjectivePairing.IntegralLift
