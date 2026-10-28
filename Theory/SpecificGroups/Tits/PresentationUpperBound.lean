module

public import Theory.SpecificGroups.Tits.R1AmbientCosetCover
public import Theory.SpecificGroups.Tits.R1SubgroupBound

/-!
# A finite upper bound for Parrott's presentation

The actual ten-generator, 37-relator presentation is covered by 1755 right
cosets of its subgroup `R₁`. The independently certified bound `|R₁| ≤ 10240`
therefore proves finiteness and the upper bound `10240 * 1755 = 17971200`.
Both covering arguments use kernel-checked equations in the presented groups.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p. 683; see `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

/-- Parrott's actual presentation is finite of order at most 17971200. -/
public theorem parrottGroup_finite_card_le :
    Finite ParrottGroup ∧ Nat.card ParrottGroup ≤ 17971200 := by
  obtain ⟨hfinite, hcard⟩ := parrottR1Subgroup_finite_card_le
  let := hfinite
  obtain ⟨hgroup, hbound⟩ := parrottAmbientR1CosetCover.finite_card_le
  refine ⟨hgroup, hbound.trans ?_⟩
  exact Nat.mul_le_mul_right 1755 hcard

/-- Finiteness follows from the certified subgroup and coset bounds. -/
public instance parrottGroup_finite : Finite ParrottGroup :=
  parrottGroup_finite_card_le.1

/-- The certified upper bound for the order of Parrott's presentation. -/
public theorem parrottGroup_card_le : Nat.card ParrottGroup ≤ 17971200 :=
  parrottGroup_finite_card_le.2

end Tits
