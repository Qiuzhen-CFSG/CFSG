module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.LiftedRelations.Derivations

/-!
# Evaluation of the 16 fixed stabilizer relators

Expand the fixed generator words and match them to the checked derivations.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.LiftedRelations

set_option maxRecDepth 100000

theorem lifted0 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 0) = 1 :=
  lifted_of_adjust 0 word12 false 64 (by decide +kernel) valid12

theorem lifted1 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 1) = 1 :=
  lifted_of_adjust 1 word13 true 43 (by decide +kernel) valid13

theorem lifted2 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 2) = 1 :=
  lifted_of_adjust 2 word0 false 0 (by decide +kernel) valid0

theorem lifted3 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 3) = 1 :=
  lifted_of_adjust 3 word0 false 0 (by decide +kernel) valid0

theorem lifted4 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 4) = 1 :=
  lifted_of_adjust 4 word0 false 0 (by decide +kernel) valid0

theorem lifted5 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 5) = 1 :=
  lifted_of_adjust 5 word33 false 85 (by decide +kernel) valid33

theorem lifted6 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 6) = 1 :=
  lifted_of_adjust 6 word19 true 43 (by decide +kernel) valid19

theorem lifted7 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 7) = 1 :=
  lifted_of_adjust 7 word100 false 19 (by decide +kernel) valid100

theorem lifted8 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 8) = 1 :=
  lifted_of_adjust 8 word102 true 93 (by decide +kernel) valid102

theorem lifted9 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 9) = 1 :=
  lifted_of_adjust 9 word108 false 64 (by decide +kernel) valid108

theorem lifted10 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 10) = 1 :=
  lifted_of_adjust 10 word1 true 3 (by decide +kernel) valid1

theorem lifted11 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 11) = 1 :=
  lifted_of_adjust 11 word74 true 94 (by decide +kernel) valid74

theorem lifted12 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 12) = 1 :=
  lifted_of_adjust 12 word29 true 111 (by decide +kernel) valid29

theorem lifted13 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 13) = 1 :=
  lifted_of_adjust 13 word87 false 2 (by decide +kernel) valid87

theorem lifted14 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 14) = 1 :=
  lifted_of_adjust 14 word59 false 92 (by decide +kernel) valid59

theorem lifted15 :
    Subgroup.CosetWordCertificate.eval level0Generator (level1Relator 15) = 1 :=
  lifted_of_adjust 15 word94 true 288 (by decide +kernel) valid94

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.LiftedRelations
