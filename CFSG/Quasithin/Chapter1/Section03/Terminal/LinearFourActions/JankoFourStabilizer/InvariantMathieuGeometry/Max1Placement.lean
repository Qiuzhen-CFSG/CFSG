module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.FixedPoints

/-!
# Assembly of invariant local placement in the J₄ max1 subgroup

Two geometric inputs suffice: a local max1 candidate exists, and each
two-power-order automorphism preserving A fixes a candidate whenever the
family is nonempty. The candidates retain an actual max1 isomorphism and the
local C-component condition for a Sylow subgroup of the overgroup. The final
construction supplies all fields of `LocalMax1Placement` in that same subgroup.

An odd-cardinality calculation for the candidate family is also sufficient,
by the cyclic two-group action proved in `Max1Placement.FixedPoints`.
Both routes are conditional; neither existence nor the concrete J₄ fixed-point
calculation is asserted here. The unconditional placement theorem remains the
assembly obligation of this module.

Source: Aschbacher–Smith, A.3.12(17) and its Sylow-overgroup proof, printed
pp.47–48, and the proof of 1.3.9, p.514; GLS3 Table 5.3i. The intrinsic
max1 certificates identify one subgroup, without proving arbitrary placement
or invariance under an automorphism stabilizing a local L₄(2) section.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
open Section02.LocalModels

/-- Conditional final assembly. The two arguments are the outstanding geometry;
the fixed-point argument receives the separately proved existence witness. -/
theorem concreteInvariantMax1Placement_of_existence_and_fixed_points
    (hexists : Max1Placement.ConcreteCandidateExistenceTheorem)
    (hfixed : Max1Placement.ConcreteCandidateFixedPointTheorem) :
    ConcreteInvariantMax1PlacementTheorem := by
  intro A S hA hlocal α htwo hfix
  obtain ⟨H, hH, hHfix⟩ := hfixed A S hA hlocal (hexists A S hA hlocal) α htwo hfix
  exact ⟨Max1Placement.placementOfFixedCandidate hH hHfix⟩

/-- An odd-cardinality calculation would discharge existence and invariance
together. It is a sufficient alternative, not an asserted J₄ calculation. -/
theorem concreteInvariantMax1Placement_of_odd_candidates
    (hodd : ∀ (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model),
      ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
      A ∈ ChapterA.Section03.localCComponents S →
      Odd (Nat.card (Max1Placement.candidates A))) :
    ConcreteInvariantMax1PlacementTheorem := by
  intro A S hA hlocal α htwo hfix
  obtain ⟨H, hH, hHfix⟩ := Max1Placement.exists_fixed_candidate_of_odd α htwo hfix
    (hodd A S hA hlocal)
  exact ⟨Max1Placement.placementOfFixedCandidate hH hHfix⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
