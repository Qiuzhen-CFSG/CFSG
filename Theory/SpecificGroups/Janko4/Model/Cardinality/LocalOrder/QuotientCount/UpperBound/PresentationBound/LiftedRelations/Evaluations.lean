module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.LiftedRelations.Derivations

/-!
# Evaluation of the 43 fixed stabilizer relators

Expand the fixed generator words and match them to the checked derivations.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.LiftedRelations

set_option maxRecDepth 100000

theorem lifted0 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 0) = 1 :=
  lifted_of_adjust 0 word1 true 3 (by decide +kernel) valid1

theorem lifted1 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 1) = 1 :=
  lifted_of_adjust 1 word0 false 0 (by decide +kernel) valid0

theorem lifted2 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 2) = 1 :=
  lifted_of_adjust 2 word2 false 47 (by decide +kernel) valid2

theorem lifted3 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 3) = 1 :=
  lifted_of_adjust 3 word16 true 3 (by decide +kernel) valid16

theorem lifted4 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 4) = 1 :=
  lifted_of_adjust 4 word17 true 30 (by decide +kernel) valid17

theorem lifted5 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 5) = 1 :=
  lifted_of_adjust 5 word18 false 192 (by decide +kernel) valid18

theorem lifted6 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 6) = 1 :=
  lifted_of_adjust 6 word26 false 69 (by decide +kernel) valid26

theorem lifted7 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 7) = 1 :=
  lifted_of_adjust 7 word27 true 3 (by decide +kernel) valid27

theorem lifted8 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 8) = 1 :=
  lifted_of_adjust 8 word21 false 108 (by decide +kernel) valid21

theorem lifted9 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 9) = 1 :=
  lifted_of_adjust 9 word6 false 523 (by decide +kernel) valid6

theorem lifted10 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 10) = 1 :=
  lifted_of_adjust 10 word28 false 226 (by decide +kernel) valid28

theorem lifted11 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 11) = 1 :=
  lifted_of_adjust 11 word39 true 187 (by decide +kernel) valid39

theorem lifted12 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 12) = 1 :=
  lifted_of_adjust 12 word15 false 327 (by decide +kernel) valid15

theorem lifted13 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 13) = 1 :=
  lifted_of_adjust 13 word43 false 247 (by decide +kernel) valid43

theorem lifted14 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 14) = 1 :=
  lifted_of_adjust 14 word46 false 3 (by decide +kernel) valid46

theorem lifted15 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 15) = 1 :=
  lifted_of_adjust 15 word51 false 222 (by decide +kernel) valid51

theorem lifted16 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 16) = 1 :=
  lifted_of_adjust 16 word58 true 632 (by decide +kernel) valid58

theorem lifted17 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 17) = 1 :=
  lifted_of_adjust 17 word47 false 8 (by decide +kernel) valid47

theorem lifted18 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 18) = 1 :=
  lifted_of_adjust 18 word61 false 157 (by decide +kernel) valid61

theorem lifted19 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 19) = 1 :=
  lifted_of_adjust 19 word62 false 69 (by decide +kernel) valid62

theorem lifted20 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 20) = 1 :=
  lifted_of_adjust 20 word63 true 142 (by decide +kernel) valid63

theorem lifted21 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 21) = 1 :=
  lifted_of_adjust 21 word37 false 293 (by decide +kernel) valid37

theorem lifted22 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 22) = 1 :=
  lifted_of_adjust 22 word72 true 30 (by decide +kernel) valid72

theorem lifted23 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 23) = 1 :=
  lifted_of_adjust 23 word73 false 405 (by decide +kernel) valid73

theorem lifted24 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 24) = 1 :=
  lifted_of_adjust 24 word75 false 114 (by decide +kernel) valid75

theorem lifted25 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 25) = 1 :=
  lifted_of_adjust 25 word77 true 485 (by decide +kernel) valid77

theorem lifted26 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 26) = 1 :=
  lifted_of_adjust 26 word83 false 398 (by decide +kernel) valid83

theorem lifted27 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 27) = 1 :=
  lifted_of_adjust 27 word85 false 360 (by decide +kernel) valid85

theorem lifted28 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 28) = 1 :=
  lifted_of_adjust 28 word88 false 669 (by decide +kernel) valid88

theorem lifted29 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 29) = 1 :=
  lifted_of_adjust 29 word93 false 3 (by decide +kernel) valid93

theorem lifted30 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 30) = 1 :=
  lifted_of_adjust 30 word97 false 365 (by decide +kernel) valid97

theorem lifted31 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 31) = 1 :=
  lifted_of_adjust 31 word99 true 567 (by decide +kernel) valid99

theorem lifted32 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 32) = 1 :=
  lifted_of_adjust 32 word102 false 439 (by decide +kernel) valid102

theorem lifted33 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 33) = 1 :=
  lifted_of_adjust 33 word114 false 3 (by decide +kernel) valid114

theorem lifted34 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 34) = 1 :=
  lifted_of_adjust 34 word123 true 814 (by decide +kernel) valid123

theorem lifted35 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 35) = 1 :=
  lifted_of_adjust 35 word125 false 152 (by decide +kernel) valid125

theorem lifted36 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 36) = 1 :=
  lifted_of_adjust 36 word129 true 513 (by decide +kernel) valid129

theorem lifted37 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 37) = 1 :=
  lifted_of_adjust 37 word131 true 53 (by decide +kernel) valid131

theorem lifted38 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 38) = 1 :=
  lifted_of_adjust 38 word140 false 765 (by decide +kernel) valid140

theorem lifted39 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 39) = 1 :=
  lifted_of_adjust 39 word145 false 582 (by decide +kernel) valid145

theorem lifted40 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 40) = 1 :=
  lifted_of_adjust 40 word151 true 598 (by decide +kernel) valid151

theorem lifted41 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 41) = 1 :=
  lifted_of_adjust 41 word155 false 763 (by decide +kernel) valid155

theorem lifted42 :
    Subgroup.CosetWordCertificate.eval subgroupGenerator (stabilizerRelator 42) = 1 :=
  lifted_of_adjust 42 word160 false 941 (by decide +kernel) valid160

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.LiftedRelations
