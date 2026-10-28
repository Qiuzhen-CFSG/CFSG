module

public import Theory.Character.AlternatingSix.Golden.Interfaces
public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry

/-!
# The intrinsic class geometry for the golden A₆ characters

The actual seven-class calculation supplies every group-theoretic input to
`goldenBlockOfCompletion`. It also supplies the class count required by the
independent irreducible-basis completion. No character-theoretic hypothesis
is needed for this construction.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
§6, pp.10–11, using the standard conjugacy calculation in A₆.
-/

namespace Theory.Character.AlternatingSix

/-- Unconditional conjugacy geometry on `alternatingGroup (Fin 6)`. -/
public theorem goldenClassGeometry : GoldenClassGeometry where
  class_count := _root_.AlternatingSix.GoldenClassGeometry.class_count
  centralizer_two := _root_.AlternatingSix.GoldenClassGeometry.centralizer_two
  centralizer_three := _root_.AlternatingSix.GoldenClassGeometry.centralizer_three
  centralizer_four := _root_.AlternatingSix.GoldenClassGeometry.centralizer_four
  centralizer_five := _root_.AlternatingSix.GoldenClassGeometry.centralizer_five
  five_inverse := _root_.AlternatingSix.GoldenClassGeometry.order_five_inverse
  five_square := _root_.AlternatingSix.GoldenClassGeometry.order_five_not_square

end Theory.Character.AlternatingSix
