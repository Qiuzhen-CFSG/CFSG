module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block000
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block016
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block032
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block048
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block064
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block080
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block096
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.MoveChecks.Block112

/-!
# All certified right-generator actions

Every compact action table carries actual seed factors. This theorem
provides the mathematical input for the independent finite coverage checks.

Source: Parrott (1972), section 5, p.683, and the parent source READMEs.
Reproduce with `RecoveryChecks/source/generate_moves.py`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction

theorem moveSound (i : Fin 122) : MoveSound i (stepData i) := by
  fin_cases i
  · exact moveSound000
  · exact moveSound001
  · exact moveSound002
  · exact moveSound003
  · exact moveSound004
  · exact moveSound005
  · exact moveSound006
  · exact moveSound007
  · exact moveSound008
  · exact moveSound009
  · exact moveSound010
  · exact moveSound011
  · exact moveSound012
  · exact moveSound013
  · exact moveSound014
  · exact moveSound015
  · exact moveSound016
  · exact moveSound017
  · exact moveSound018
  · exact moveSound019
  · exact moveSound020
  · exact moveSound021
  · exact moveSound022
  · exact moveSound023
  · exact moveSound024
  · exact moveSound025
  · exact moveSound026
  · exact moveSound027
  · exact moveSound028
  · exact moveSound029
  · exact moveSound030
  · exact moveSound031
  · exact moveSound032
  · exact moveSound033
  · exact moveSound034
  · exact moveSound035
  · exact moveSound036
  · exact moveSound037
  · exact moveSound038
  · exact moveSound039
  · exact moveSound040
  · exact moveSound041
  · exact moveSound042
  · exact moveSound043
  · exact moveSound044
  · exact moveSound045
  · exact moveSound046
  · exact moveSound047
  · exact moveSound048
  · exact moveSound049
  · exact moveSound050
  · exact moveSound051
  · exact moveSound052
  · exact moveSound053
  · exact moveSound054
  · exact moveSound055
  · exact moveSound056
  · exact moveSound057
  · exact moveSound058
  · exact moveSound059
  · exact moveSound060
  · exact moveSound061
  · exact moveSound062
  · exact moveSound063
  · exact moveSound064
  · exact moveSound065
  · exact moveSound066
  · exact moveSound067
  · exact moveSound068
  · exact moveSound069
  · exact moveSound070
  · exact moveSound071
  · exact moveSound072
  · exact moveSound073
  · exact moveSound074
  · exact moveSound075
  · exact moveSound076
  · exact moveSound077
  · exact moveSound078
  · exact moveSound079
  · exact moveSound080
  · exact moveSound081
  · exact moveSound082
  · exact moveSound083
  · exact moveSound084
  · exact moveSound085
  · exact moveSound086
  · exact moveSound087
  · exact moveSound088
  · exact moveSound089
  · exact moveSound090
  · exact moveSound091
  · exact moveSound092
  · exact moveSound093
  · exact moveSound094
  · exact moveSound095
  · exact moveSound096
  · exact moveSound097
  · exact moveSound098
  · exact moveSound099
  · exact moveSound100
  · exact moveSound101
  · exact moveSound102
  · exact moveSound103
  · exact moveSound104
  · exact moveSound105
  · exact moveSound106
  · exact moveSound107
  · exact moveSound108
  · exact moveSound109
  · exact moveSound110
  · exact moveSound111
  · exact moveSound112
  · exact moveSound113
  · exact moveSound114
  · exact moveSound115
  · exact moveSound116
  · exact moveSound117
  · exact moveSound118
  · exact moveSound119
  · exact moveSound120
  · exact moveSound121

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
