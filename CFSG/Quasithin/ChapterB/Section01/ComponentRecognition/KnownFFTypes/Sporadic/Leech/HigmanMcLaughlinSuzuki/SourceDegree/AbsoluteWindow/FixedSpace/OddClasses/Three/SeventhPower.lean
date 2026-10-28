module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three.Words
import all CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three.Words

/-!
# Seventh-power fusion of the marked HS fifteen-element

The existing square conjugator covers four of the eight generators of the
marked cyclic fifteen-group. The word below connects the remaining four.
Together these identities supply the power-fusion step in `OddClasses.Three`.

GAP supplies only a carrier word; Lean checks its conjugation identity on all
100 letters. The inverse-generator left-action convention is unchanged.
Source: ATLAS HSG1-p100B0, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
The discovery script and original output are retained in `source/`.
The internal import lets this certificate reduce the existing private transport
word inside `fifteen`; only the conjugacy theorem is added to the public API.
-/

public section
namespace Sporadic.LeechRelated.HS.OddClassBound.Three
open ThreePowerFusion Theory.GroupTheory OrderCertificate

private def letter (i : Fin 3) : Carrier := if i = 0 then a else if i = 1 then b else b⁻¹
private def seventhActor : Carrier := evalWord letter
  [2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2,
  2, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1,
  0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2,
  0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0,
  1, 0, 2, 0, 2, 0]

/-- A literal carrier word raises the marked fifteen-element to its seventh power. -/
theorem fifteen_seventh : IsConj fifteen (fifteen ^ 7) := by
  apply isConj_iff.mpr
  refine ⟨seventhActor, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.HS.OddClassBound.Three
