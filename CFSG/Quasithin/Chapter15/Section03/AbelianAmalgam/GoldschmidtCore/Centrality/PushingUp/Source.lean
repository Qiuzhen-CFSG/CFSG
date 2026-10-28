module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Control

/-!
# Discharging the actual doubled-natural pushing-up input

The Chapter C source theorem uses exactly the compatible quotient and
module coordinates required by the 15.3.68 character-kernel consumer.
Its characteristic alternative is literal normality inside that same
ambient group; its other alternative is equality with the original
component's commutator core. This instantiates the existing universal
source input without adding a model or control premise.

Source: Aschbacher--Smith C.1.37(1),(3), applied in 15.3.68(2),
printed pp.141--143 and 1154--1155.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
universe u

/-- The doubled-natural source implication used by the original terminal
character kernel is proved for every specified known-simple class. -/
theorem doubledNaturalSource (κ : GroupClass.{u}) : DoubledNaturalSource κ := by
  intro K _ _ hSQ L P U _ _ T hL hfit hgen hmax hTP eK eL hcompat hinner
    hU hred hcomm hne eU hact
  let d : ChapterC.DoubledNaturalControl.SourceReduction.SourceData κ L P U T :=
    { sqtk := hSQ
      component := hL
      fitting := hfit
      generation := hgen
      maximal := hmax
      sylow_le := hTP
      eK := eK
      eL := eL
      quotient_compatible := hcompat
      quotient_inner := hinner
      elementary := hU
      action_reduced := hred
      commutator := hcomm
      nontrivial := hne
      eU := eU
      action := hact }
  exact d.control.imp_right Or.inr

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
