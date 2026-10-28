module

public import Theory.Representation.PSL3Two.DoubledOffenders
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Action

/-!
# The doubled-normalizer calculation on the actual T_v image

Apply the intrinsic Sylow theorem to the faithful full action specified by
`ExtendedCoordinates`. The diagonal containment, normalizer containment and
Sylow-image identity are precisely the ones in `Thompson.Action`. This supplies
all-offender uniqueness and the full T_v pointwise-fixer equality needed to
restrict offenders from W_K to U_K and then apply B.2.20.

The construction of compatible coordinates, transport back to the actual plus
quotient and W_K, and final Thompson/Baumann identifications remain with the
source assembly. No conclusion about those original groups is assumed here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.20, printed p.931; B.2.20, printed p.82.
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection
variable {G : Type*} [_root_.Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}
    {e : EarlierData K L T z v}
    {d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed}
namespace ExtendedCoordinates
variable (c : ExtendedCoordinates e d)
theorem model_offenders : ∃ g : BinaryLinearThree.Group,
    let A := (R.map (MulAut.conj g).toMonoidHom).map (W.prod W).asGroupHom
    let S := (plusImage K L T z v e.normalizeL e.fixSeed (Tv T v)).map c.action
    A ≤ S ∧
    (∀ E : Subgroup DoubledOffenders.D, E ≤ S →
      (IsOffender DoubledOffenders.τ E ↔ E = A)) ∧
    (∀ x ∈ S, (∀ u ∈ fixedSpace DoubledOffenders.τ A, DoubledOffenders.τ x u = u) ↔
      x ∈ A) := by
  obtain ⟨P, hP⟩ := c.sylow_image
  simpa only [hP] using DoubledOffenders.sylow_offenders c.action.range
    c.diagonal_le_range c.normalizes_diagonal P

/-- The full T_v action image has the exact pointwise fixer required in B.2.20. -/
theorem model_offenders_and_fixer : ∃ g : BinaryLinearThree.Group,
    let A := (R.map (MulAut.conj g).toMonoidHom).map (W.prod W).asGroupHom
    let S := (plusImage K L T z v e.normalizeL e.fixSeed (Tv T v)).map c.action
    A ≤ S ∧
    (∀ E : Subgroup DoubledOffenders.D, E ≤ S →
      (IsOffender DoubledOffenders.τ E ↔ E = A)) ∧
    S ⊓ DoubledOffenders.pointwiseFixer (fixedSpace DoubledOffenders.τ A) = A := by
  obtain ⟨P, hP⟩ := c.sylow_image
  simpa only [hP] using DoubledOffenders.sylow_offenders_and_fixer c.action.range
    c.diagonal_le_range c.normalizes_diagonal P
end ExtendedCoordinates
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
