module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Assembly
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.Recognition
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition

/-!
# Hexacode coordinates from the terminal source alternatives

The genuine surviving full quotient and the corrected FF classification on
the literal offender action give an exceptional case. Transporting the
original quotient representation along its actor equivalence produces a
faithful binary representation with an irreducible even restriction and
dimension six. Intrinsic representation recognition supplies coordinates
intertwining the full action, including the odd coset.

The resulting group automorphism preserves the even cover, which is the
commutator subgroup. Consequently the same coordinates identify the image
of the actual Thompson subgroup with that cover. This constructs all fields
of `HexacodeCoordinates` without an additional representation-equivalence or
cover-comparison premise.

The local 15.3.66--68 data and the full quotient and FF classification
alternatives remain explicit inputs. Their source construction and the
marked-plane argument belong to the final source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155 (PDF p.1172), using B.5.1/B.5.6,
printed pp.99 and 105, and K.1.3, printed p.453 (PDF p.464).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition

variable {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- Intrinsic six-dimensional recognition constructs full action coordinates
on the original module and preserves the actual Thompson image. -/
theorem ExceptionalCase.nonempty_coordinates {d : SourceInput V} (c : ExceptionalCase d) :
    Nonempty (HexacodeCoordinates V d.centralizer_isTwoGroup d.core_centralizes) := by
  obtain ⟨a, e, he⟩ := Representation.Hexacode.SixDimensional.exists_equivariant
    c.modelAction c.modelAction_injective c.modelAction_even_irreducible c.dimension
  exact ⟨c.coordinatesOfModelEquivalence a e he⟩

/-- The genuine four-way source quotient alternative and the corrected full
FF witness on the literal offender representation yield hexacode coordinates.
Ordinary-module exclusion, the source cover comparison, full representation
recognition and the Thompson-image identification are all discharged. -/
theorem SourceInput.nonempty_coordinates_of_surviving_source (d : SourceInput V)
    (quotient : Cases.SurvivingQuotientAlternative (coreQuotient H))
    (classification : Intersection.SourceFFAlternative d.offenderAction) :
    Nonempty (HexacodeCoordinates V d.centralizer_isTwoGroup d.core_centralizes) := by
  obtain ⟨c⟩ := TripleCover.SourceAdapter.exceptionalCase_of_surviving_source_models
    d quotient classification
  exact c.nonempty_coordinates

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
