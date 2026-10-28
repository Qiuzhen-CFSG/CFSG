module

public import Theory.SpecificGroups.G2Five.AtlasBoundSubgroup
public import Theory.GroupTheory.PresentedGroupBounds

/-!
# Assembly of a cardinal bound for the retained ATLAS presentation

A certified cover by 3906 representatives and a bound of 1500000 on the
explicit two-word subgroup imply finiteness and the bound 5859000000 on the
abstract presentation. The two premises are independent proof obligations;
neither is supplied by an action on 3906 points alone.

The proof uses the surjection from subgroup elements paired with coset
representatives, as formalized in `PresentedGroupBounds`.
Source for the chosen words: `AtlasBoundSource/README.md`.
-/

namespace G2Five.AtlasPresentation

/-- Assemble the order bound from the subgroup and ambient coset certificates. -/
public theorem finite_card_Model_le_of_boundSubgroup
    (hlocal : Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 1500000)
    (cover : Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 3906)) :
    Finite Model ∧ Nat.card Model ≤ 5859000000 := by
  let := hlocal.1
  have hgen : Subgroup.closure (Set.range generator) = ⊤ :=
    PresentedGroup.closure_range_of (Set.range relator)
  obtain ⟨hfinite, hcard⟩ := cover.finite_card_le hgen
  refine ⟨hfinite, ?_⟩
  calc
    Nat.card Model ≤ Nat.card boundSubgroup * 3906 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hcard
    _ ≤ 1500000 * 3906 := Nat.mul_le_mul_right 3906 hlocal.2
    _ = 5859000000 := rfl

end G2Five.AtlasPresentation
