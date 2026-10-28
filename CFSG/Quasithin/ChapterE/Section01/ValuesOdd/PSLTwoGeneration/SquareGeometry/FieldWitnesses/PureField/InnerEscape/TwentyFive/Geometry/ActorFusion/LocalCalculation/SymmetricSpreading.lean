module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalCalculation.Coordinates
public import Theory.SpecificGroups.SymmetricFive.LocalGraphSpreading

/-!
# Conjugate joins in the characteristic-five local product

The finite S₅ × C₂ calculation supplies the exact spreading premise used by
`local_spread_of_symmetricSpreading`. It includes transport to the supplied
Sylow subgroup and any order-two factor. The first projection and exclusion
of the zero graph are precisely those established by the intrinsic marking
in `Coordinates`; no further placement or generation premise is introduced.

Source: Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed pp.210--214,
citing Aschbacher (1982), Lemma 4.10. This is the finite local input; the
field-model assembly and the full source theorem retain their own owners.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

/-- The unconditional symmetric-product calculation for any order-two factor. -/
theorem symmetricSpreading_of_card_two (Z : Type*) [Group Z]
    (hZ : Nat.card Z = 2) : ActorFusion.SymmetricSpreading Z :=
  Theory.SpecificGroups.SymmetricFive.LocalGraphSpreading.spreading_of_card_two Z hZ

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
