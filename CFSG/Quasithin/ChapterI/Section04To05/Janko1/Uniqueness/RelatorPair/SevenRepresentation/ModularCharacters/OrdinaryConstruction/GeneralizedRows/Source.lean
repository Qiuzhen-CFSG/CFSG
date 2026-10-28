module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.CyclicRestrictions
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.NilpotentSubgroups
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerLabels

/-!
# Genuine generalized ordinary rows for the source group

For the arbitrary finite simple group with the stated involution centralizer,
order and involution fusion, the supplied class census admits compatible labels
under which every ordinary table row is a genuine generalized character.

The power-label construction aligns actual powers of the class representatives.
Exact cyclic Fourier identities realize the restrictions using integer
combinations of linear characters. Every nilpotent subgroup is cyclic or has
exponent dividing two and order dividing eight; the latter restrictions are
integer combinations of regular and principal characters. Brauer's nilpotent
restriction criterion then constructs differences of actual complex
representation characters on the ambient group.

This discharges every local input of `ordinaryGeneralizedRows_of_local_restrictions`.
The actual class enumeration remains the explicit input `c`; its construction
and the assembly of the irreducible ordinary table belong to
`OrdinaryConstruction`. This extension keeps the shared local criterion
available to its prerequisite modules without a circular import.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482. The original detailed
calculation was not recovered; the proof above reconstructs this step. Numerical
conventions and attribution are recorded in `../../Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Every ordinary row is a difference of genuine representation characters of
the arbitrary source group, with a single compatible labeling of its classes.
Only the class enumeration remains explicit. -/
public theorem ordinaryGeneralizedRows_of_source {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (h : CFSG.Quasithin.Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z)
    (c : OrdinaryClassData G) : Nonempty (OrdinaryGeneralizedRows c) := by
  obtain ⟨p⟩ := ordinaryPowerLabels_of_source h horder hfusion c
  exact ordinaryGeneralizedRows_of_powerLabels_and_nilpotent_types p
    (ordinary_nilpotent_subgroup_types h horder c)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
