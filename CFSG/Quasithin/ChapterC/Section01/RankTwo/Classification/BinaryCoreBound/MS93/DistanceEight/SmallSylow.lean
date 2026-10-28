module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.CentralFourObstruction

/-!
# Central four obstruction for the original binary MS input

The larger-distance argument supplies an included four-group in the original
local group.  Once the original two-core fixes it, MS3 rules it out because the
radical is a full Sylow subgroup with central omega subgroup of order at most
four.  This is the shared final step in the original 15.3.23–25 applications
of MS93, (4.4); the prescribed replacement and original-core action remain
explicit geometric inputs.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
universe u
variable {J : Type u} [Group J] [Finite J]

namespace BinaryMS.MS93.InputSetup
open DistanceEight.PathCentrality
variable {κ : GroupClass.{u}} {L R : Subgroup J} {h : Input κ L R}
    (t : InputSetup h)

/-- The literal included factor contradicts original MS3 after the original
two-core action has been discharged. -/
theorem false_of_small_sylow_and_core_action
    (P : Sylow 2 J) (hP : R = (P : Subgroup J))
    (hsmall : Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup J)) ≤ 4)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hcore : t.reducedCentralFour ≤ centralizer (pCore 2 J : Set J)) : False := by
  let := t.reducedCentralFour_elementary common earlier
  exact h.no_central_four_of_sylow P hP hsmall t.reducedCentralFour
    (t.reducedCentralFour_card common earlier)
    (t.reducedCentralFour_le_center_of_centralizes_core earlier hcore)

/-- The common larger-distance source consumer needs only the two genuine
remaining geometric inputs: prescribed replacement and original-core action. -/
theorem false_of_large_distance_of_replacement_and_core_action
    (P : Sylow 2 J) (hP : R = (P : Subgroup J))
    (hsmall : Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup J)) ≤ 4)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (replacement : ∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p)
    (hcore : t.reducedCentralFour ≤ centralizer (pCore 2 J : Set J)) : False :=
  t.false_of_small_sylow_and_core_action P hP hsmall common
    (Source44.SourceEarlier.earlier common hb replacement) hcore

end BinaryMS.MS93.InputSetup
end CFSG.Quasithin.ChapterC
