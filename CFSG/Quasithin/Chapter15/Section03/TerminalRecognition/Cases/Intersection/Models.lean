module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Source

/-!
# Output models for the terminal intersection

These are specifications of the required comparison outputs, not source
hypotheses or classification theorems. Every ordinary case carries an
isomorphism of the actual group. The hatted cases retain the source's
perfect central triple cover and its symmetric extension with the sign
action on the cubic kernel. Their comparison with the concrete hexacode
carriers belongs to the existing exceptional-action construction.

The SL₃(2) carrier denotes the source L₃(2); its scalar center is trivial.
The original full B.5.6 action witness remains on the same representation
throughout comparison, including in the triple-cover branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; triple-cover convention A.3.5, printed p.43.
-/

public section
open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- The seven non-S₃ possibilities for the actual Thompson image. -/
inductive NonS3ImageAlternative (D : Type*) [Group D] : Prop
  | linearThree (equiv : D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  | alternatingSix (equiv : D ≃* alternatingGroup (Fin 6))
  | symmetricSix (equiv : D ≃* Equiv.Perm (Fin 6))
  | alternatingSeven (equiv : D ≃* alternatingGroup (Fin 7))
  | symmetricSeven (equiv : D ≃* Equiv.Perm (Fin 7))
  | tripleSix (cover : FSource.TripleAlternating D 6)
  | g2Two (equiv : D ≃* Atlas.G2.Model (ZMod 2))

/-- The ambient quotient possibilities before the separate marked-local
exclusion removes the four perfect cases. Triple covers are actual covering
witnesses; no comparison with an unconnected family label is allowed. -/
inductive AmbientAlternative (D : Type*) [Group D] : Prop
  | linearThree (equiv : D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  | alternatingSix (equiv : D ≃* alternatingGroup (Fin 6))
  | alternatingSeven (equiv : D ≃* alternatingGroup (Fin 7))
  | tripleAlternatingSix (cover : FSource.TripleAlternating D 6)
  | symmetricSix (equiv : D ≃* Equiv.Perm (Fin 6))
  | tripleSymmetricSix (cover : FSource.TripleSymmetric D 6)
  | symmetricSeven (equiv : D ≃* Equiv.Perm (Fin 7))
  | g2Two (equiv : D ≃* Atlas.G2.Model (ZMod 2))

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
