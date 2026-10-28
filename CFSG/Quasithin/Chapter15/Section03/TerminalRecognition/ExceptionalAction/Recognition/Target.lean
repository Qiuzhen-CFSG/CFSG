module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions

/-!
# Target of the terminal action recognition

The required coordinates identify the full quotient action with the hexacode
action and identify the image of the actual elementary Thompson subgroup
with the even cover. Keeping these two actor groups separate is essential:
B.5.1 applies to the offender-generated group, not automatically to the
whole quotient. This structure specifies the output of recognition; it
does not assert existence of the coordinates or any classification theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155 (PDF p.1172).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction

open Subgroup Atlas.Codes
open scoped IsMulCommutative

variable {H : Type*} [Group H]

/-- The action-recognition conclusion, including the actual Thompson image.
Its construction from the source hypotheses is a separate proof obligation. -/
structure HexacodeCoordinates (V : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure V)]
    (hC : IsPGroup 2 (centralizer (V : Set H)))
    (hcore : pCore 2 H ≤ centralizer (V : Set H)) where
  actor : coreQuotient H ≃* HexAutomorphisms
  vectors : Additive (moduleClosure V) ≃ₗ[ZMod 2] hexacode
  equivariant : ∀ g v, vectors (quotientAction V hC hcore g v) =
    Representation.Hexacode.action (actor g) (vectors v)
  thompson_image : ((thompsonGroup H).map coreProjection).map actor.toMonoidHom =
    hexSign.ker

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction
