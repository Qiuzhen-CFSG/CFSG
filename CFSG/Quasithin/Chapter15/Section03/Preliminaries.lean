module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ActionQuotient

/-!
# Assembly boundary for the preliminaries of Section 15.3

The natural-action input retains the full matrix action on the two binary
planes. The checked elementary arguments prove the central-omega equality
of 15.3.8 and the centralizer, quotient-normalizer, and characteristic-subgroup
steps of 15.3.11 from their displayed local inputs.

The complete source results 15.3.2–12 still require the orthogonal Thompson
calculation, the residual alternatives, the exclusion of the `S₄` wreath
configuration, and the outside-overgroup and component analysis. These are
not assumptions hidden in the natural-action interface. This module retains
their final assembly; no source result is certified merely by an input record.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1121–1125.
-/

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

/-- The full ambient conclusion of 15.3.8, with its natural-action facts
explicit until the preceding orthogonal calculation supplies them. -/
public theorem lemma_15_3_8_of_plane_facts
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (V V₁ : Subgroup G)
    (hindex : ((planeStabilizer T V₁).subgroupOf (T : Subgroup G)).index = 2)
    (hZ : Nat.card (centralInvolutions T) = 2)
    [IsElementaryAbelian 2 (fixedPlane V (planeStabilizer T V₁))]
    (hfixed : fixedPlane V (planeStabilizer T V₁) ≤ planeStabilizer T V₁)
    (hcard : Nat.card (fixedPlane V (planeStabilizer T V₁)) = 4) :
    fixedPlane V (planeStabilizer T V₁) = centralOmegaIn (planeStabilizer T V₁) ∧
      Nonempty (fixedPlane V (planeStabilizer T V₁) ≃* OrthogonalPlaneVector) := by
  refine ⟨fixedPlane_eq_centralOmegaIn T V _ inf_le_left hindex hZ hfixed hcard, ?_⟩
  obtain ⟨e, _⟩ := FourGroupMatrixCoordinates.exists_four_group_matrix_coordinates hcard
  exact ⟨e⟩

end CFSG.Quasithin.Chapter15.Section03
