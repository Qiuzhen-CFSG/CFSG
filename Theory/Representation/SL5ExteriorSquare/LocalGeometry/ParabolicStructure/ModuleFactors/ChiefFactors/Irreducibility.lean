module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.MiddleTensor
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.LastChiefFactor

/-!
# The chief filtration of the first exterior stabilizer

For the genuine exterior square of the natural `SL₅(F₂)` module, the stabilizer
of `V₁ = Λ²(Γ₂)` has the strict invariant chief filtration `0 < V₁ < V₇ < V`.
The factors carry the literal restricted and quotient actions of the two-space
parabolic, which equals this exterior stabilizer.

The first factor is one-dimensional. The middle factor is identified, through
its mixed wedge coordinates, with the tensor of the two natural block modules;
block transvections prove its irreducibility. Complementary-wedge coordinates
identify the last factor with the dual-natural lower-block module. The theorem
below assembles these proofs with strictness and invariance, discharging both
factor premises of `exteriorStabilizer_V₁_chief_chain_with_factors`.

Source: Aschbacher–Smith, Lemma 12.5.2(1), printed p.817/PDF p.834, the chief-series
clause in the concrete exterior-square model. Transport to the source ambient
group and the other clauses of that lemma belong to the source assembly.
-/

public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The first exterior stabilizer preserves the strict chain `0 < V₁ < V₇ < V`,
and all three actual induced factors are irreducible. No factor hypothesis
remains in this intrinsic chief-series statement. -/
theorem exteriorStabilizer_V₁_chief_chain :
    exteriorStabilizer V₁ = parabolic 2 ∧
      ((⊥ : Submodule (ZMod 2) V) < V₁ ∧ V₁ < V₇ ∧ V₇ < ⊤) ∧
      exteriorStabilizer V₁ ≤ exteriorStabilizer V₇ ∧
      Representation.IsIrreducible firstChiefFactor ∧
      Representation.IsIrreducible middleChiefFactor ∧
      Representation.IsIrreducible lastChiefFactor :=
  exteriorStabilizer_V₁_chief_chain_with_factors
    middleChiefFactor_isIrreducible lastChiefFactor_isIrreducible

end Representation.SL5ExteriorSquare
