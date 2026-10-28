module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Checks111
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family5
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion.Families.Family6

/-!
# Invertibility from the fixed degree-1792 elimination certificate

The elimination criterion is applied to the literal `packedCompletion`, with
its original row convention and the exact update `nucleus` times the zeroth
coordinate covector. The final sixteen pivots are checked in `Checks111`.
The seven check families supply all preceding pivots. Together they prove
`packedCompletion_isUnit` without additional hypotheses.

Source, certificate reproduction and measurements: `Completion/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate
open CompletionElimination CompletionCertificate

/-- The first 111 numerical blocks, complementary to the final checked block. -/
def CompletionBlockChecks : Prop := ∀ k, k < 111 → blockCheck k = true

/-- The seven independently checked families cover the first 111 blocks. -/
theorem completionBlockChecks : CompletionBlockChecks := by
  intro k hk
  by_cases h0 : k < 16
  · exact checksFamily0 k (Nat.zero_le _) h0
  by_cases h1 : k < 32
  · exact checksFamily1 k (by omega) h1
  by_cases h2 : k < 48
  · exact checksFamily2 k (by omega) h2
  by_cases h3 : k < 64
  · exact checksFamily3 k (by omega) h3
  by_cases h4 : k < 80
  · exact checksFamily4 k (by omega) h4
  by_cases h5 : k < 96
  · exact checksFamily5 k (by omega) h5
  exact checksFamily6 k (by omega) hk

/-- Assemble the bounded checks into all 1792 pivot equations. -/
theorem completion_state_of_blockChecks
    (h : CompletionBlockChecks) (w : Fin 1792 → ZMod 2)
    (hsource : ∀ i, i < 1792 → dot (originalRow i) w = 0) :
    State 1792 basis112 w := by
  have hall : ∀ k, k < 112 → blockCheck k = true := by
    intro k hk
    by_cases hk' : k < 111
    · exact h k hk'
    · have he : k = 111 := by omega
      subst k
      exact block111_checked
  have s000 : State 0 basis000 w := state_zero w
  have s001 : State 16 basis001 w :=
    checkEntries_sound originalRow w hsource 0 basis000 block000
      (hall 0 (by decide)) s000
  have s002 : State 32 basis002 w :=
    checkEntries_sound originalRow w hsource 16 basis001 block001
      (hall 1 (by decide)) s001
  have s003 : State 48 basis003 w :=
    checkEntries_sound originalRow w hsource 32 basis002 block002
      (hall 2 (by decide)) s002
  have s004 : State 64 basis004 w :=
    checkEntries_sound originalRow w hsource 48 basis003 block003
      (hall 3 (by decide)) s003
  have s005 : State 80 basis005 w :=
    checkEntries_sound originalRow w hsource 64 basis004 block004
      (hall 4 (by decide)) s004
  have s006 : State 96 basis006 w :=
    checkEntries_sound originalRow w hsource 80 basis005 block005
      (hall 5 (by decide)) s005
  have s007 : State 112 basis007 w :=
    checkEntries_sound originalRow w hsource 96 basis006 block006
      (hall 6 (by decide)) s006
  have s008 : State 128 basis008 w :=
    checkEntries_sound originalRow w hsource 112 basis007 block007
      (hall 7 (by decide)) s007
  have s009 : State 144 basis009 w :=
    checkEntries_sound originalRow w hsource 128 basis008 block008
      (hall 8 (by decide)) s008
  have s010 : State 160 basis010 w :=
    checkEntries_sound originalRow w hsource 144 basis009 block009
      (hall 9 (by decide)) s009
  have s011 : State 176 basis011 w :=
    checkEntries_sound originalRow w hsource 160 basis010 block010
      (hall 10 (by decide)) s010
  have s012 : State 192 basis012 w :=
    checkEntries_sound originalRow w hsource 176 basis011 block011
      (hall 11 (by decide)) s011
  have s013 : State 208 basis013 w :=
    checkEntries_sound originalRow w hsource 192 basis012 block012
      (hall 12 (by decide)) s012
  have s014 : State 224 basis014 w :=
    checkEntries_sound originalRow w hsource 208 basis013 block013
      (hall 13 (by decide)) s013
  have s015 : State 240 basis015 w :=
    checkEntries_sound originalRow w hsource 224 basis014 block014
      (hall 14 (by decide)) s014
  have s016 : State 256 basis016 w :=
    checkEntries_sound originalRow w hsource 240 basis015 block015
      (hall 15 (by decide)) s015
  have s017 : State 272 basis017 w :=
    checkEntries_sound originalRow w hsource 256 basis016 block016
      (hall 16 (by decide)) s016
  have s018 : State 288 basis018 w :=
    checkEntries_sound originalRow w hsource 272 basis017 block017
      (hall 17 (by decide)) s017
  have s019 : State 304 basis019 w :=
    checkEntries_sound originalRow w hsource 288 basis018 block018
      (hall 18 (by decide)) s018
  have s020 : State 320 basis020 w :=
    checkEntries_sound originalRow w hsource 304 basis019 block019
      (hall 19 (by decide)) s019
  have s021 : State 336 basis021 w :=
    checkEntries_sound originalRow w hsource 320 basis020 block020
      (hall 20 (by decide)) s020
  have s022 : State 352 basis022 w :=
    checkEntries_sound originalRow w hsource 336 basis021 block021
      (hall 21 (by decide)) s021
  have s023 : State 368 basis023 w :=
    checkEntries_sound originalRow w hsource 352 basis022 block022
      (hall 22 (by decide)) s022
  have s024 : State 384 basis024 w :=
    checkEntries_sound originalRow w hsource 368 basis023 block023
      (hall 23 (by decide)) s023
  have s025 : State 400 basis025 w :=
    checkEntries_sound originalRow w hsource 384 basis024 block024
      (hall 24 (by decide)) s024
  have s026 : State 416 basis026 w :=
    checkEntries_sound originalRow w hsource 400 basis025 block025
      (hall 25 (by decide)) s025
  have s027 : State 432 basis027 w :=
    checkEntries_sound originalRow w hsource 416 basis026 block026
      (hall 26 (by decide)) s026
  have s028 : State 448 basis028 w :=
    checkEntries_sound originalRow w hsource 432 basis027 block027
      (hall 27 (by decide)) s027
  have s029 : State 464 basis029 w :=
    checkEntries_sound originalRow w hsource 448 basis028 block028
      (hall 28 (by decide)) s028
  have s030 : State 480 basis030 w :=
    checkEntries_sound originalRow w hsource 464 basis029 block029
      (hall 29 (by decide)) s029
  have s031 : State 496 basis031 w :=
    checkEntries_sound originalRow w hsource 480 basis030 block030
      (hall 30 (by decide)) s030
  have s032 : State 512 basis032 w :=
    checkEntries_sound originalRow w hsource 496 basis031 block031
      (hall 31 (by decide)) s031
  have s033 : State 528 basis033 w :=
    checkEntries_sound originalRow w hsource 512 basis032 block032
      (hall 32 (by decide)) s032
  have s034 : State 544 basis034 w :=
    checkEntries_sound originalRow w hsource 528 basis033 block033
      (hall 33 (by decide)) s033
  have s035 : State 560 basis035 w :=
    checkEntries_sound originalRow w hsource 544 basis034 block034
      (hall 34 (by decide)) s034
  have s036 : State 576 basis036 w :=
    checkEntries_sound originalRow w hsource 560 basis035 block035
      (hall 35 (by decide)) s035
  have s037 : State 592 basis037 w :=
    checkEntries_sound originalRow w hsource 576 basis036 block036
      (hall 36 (by decide)) s036
  have s038 : State 608 basis038 w :=
    checkEntries_sound originalRow w hsource 592 basis037 block037
      (hall 37 (by decide)) s037
  have s039 : State 624 basis039 w :=
    checkEntries_sound originalRow w hsource 608 basis038 block038
      (hall 38 (by decide)) s038
  have s040 : State 640 basis040 w :=
    checkEntries_sound originalRow w hsource 624 basis039 block039
      (hall 39 (by decide)) s039
  have s041 : State 656 basis041 w :=
    checkEntries_sound originalRow w hsource 640 basis040 block040
      (hall 40 (by decide)) s040
  have s042 : State 672 basis042 w :=
    checkEntries_sound originalRow w hsource 656 basis041 block041
      (hall 41 (by decide)) s041
  have s043 : State 688 basis043 w :=
    checkEntries_sound originalRow w hsource 672 basis042 block042
      (hall 42 (by decide)) s042
  have s044 : State 704 basis044 w :=
    checkEntries_sound originalRow w hsource 688 basis043 block043
      (hall 43 (by decide)) s043
  have s045 : State 720 basis045 w :=
    checkEntries_sound originalRow w hsource 704 basis044 block044
      (hall 44 (by decide)) s044
  have s046 : State 736 basis046 w :=
    checkEntries_sound originalRow w hsource 720 basis045 block045
      (hall 45 (by decide)) s045
  have s047 : State 752 basis047 w :=
    checkEntries_sound originalRow w hsource 736 basis046 block046
      (hall 46 (by decide)) s046
  have s048 : State 768 basis048 w :=
    checkEntries_sound originalRow w hsource 752 basis047 block047
      (hall 47 (by decide)) s047
  have s049 : State 784 basis049 w :=
    checkEntries_sound originalRow w hsource 768 basis048 block048
      (hall 48 (by decide)) s048
  have s050 : State 800 basis050 w :=
    checkEntries_sound originalRow w hsource 784 basis049 block049
      (hall 49 (by decide)) s049
  have s051 : State 816 basis051 w :=
    checkEntries_sound originalRow w hsource 800 basis050 block050
      (hall 50 (by decide)) s050
  have s052 : State 832 basis052 w :=
    checkEntries_sound originalRow w hsource 816 basis051 block051
      (hall 51 (by decide)) s051
  have s053 : State 848 basis053 w :=
    checkEntries_sound originalRow w hsource 832 basis052 block052
      (hall 52 (by decide)) s052
  have s054 : State 864 basis054 w :=
    checkEntries_sound originalRow w hsource 848 basis053 block053
      (hall 53 (by decide)) s053
  have s055 : State 880 basis055 w :=
    checkEntries_sound originalRow w hsource 864 basis054 block054
      (hall 54 (by decide)) s054
  have s056 : State 896 basis056 w :=
    checkEntries_sound originalRow w hsource 880 basis055 block055
      (hall 55 (by decide)) s055
  have s057 : State 912 basis057 w :=
    checkEntries_sound originalRow w hsource 896 basis056 block056
      (hall 56 (by decide)) s056
  have s058 : State 928 basis058 w :=
    checkEntries_sound originalRow w hsource 912 basis057 block057
      (hall 57 (by decide)) s057
  have s059 : State 944 basis059 w :=
    checkEntries_sound originalRow w hsource 928 basis058 block058
      (hall 58 (by decide)) s058
  have s060 : State 960 basis060 w :=
    checkEntries_sound originalRow w hsource 944 basis059 block059
      (hall 59 (by decide)) s059
  have s061 : State 976 basis061 w :=
    checkEntries_sound originalRow w hsource 960 basis060 block060
      (hall 60 (by decide)) s060
  have s062 : State 992 basis062 w :=
    checkEntries_sound originalRow w hsource 976 basis061 block061
      (hall 61 (by decide)) s061
  have s063 : State 1008 basis063 w :=
    checkEntries_sound originalRow w hsource 992 basis062 block062
      (hall 62 (by decide)) s062
  have s064 : State 1024 basis064 w :=
    checkEntries_sound originalRow w hsource 1008 basis063 block063
      (hall 63 (by decide)) s063
  have s065 : State 1040 basis065 w :=
    checkEntries_sound originalRow w hsource 1024 basis064 block064
      (hall 64 (by decide)) s064
  have s066 : State 1056 basis066 w :=
    checkEntries_sound originalRow w hsource 1040 basis065 block065
      (hall 65 (by decide)) s065
  have s067 : State 1072 basis067 w :=
    checkEntries_sound originalRow w hsource 1056 basis066 block066
      (hall 66 (by decide)) s066
  have s068 : State 1088 basis068 w :=
    checkEntries_sound originalRow w hsource 1072 basis067 block067
      (hall 67 (by decide)) s067
  have s069 : State 1104 basis069 w :=
    checkEntries_sound originalRow w hsource 1088 basis068 block068
      (hall 68 (by decide)) s068
  have s070 : State 1120 basis070 w :=
    checkEntries_sound originalRow w hsource 1104 basis069 block069
      (hall 69 (by decide)) s069
  have s071 : State 1136 basis071 w :=
    checkEntries_sound originalRow w hsource 1120 basis070 block070
      (hall 70 (by decide)) s070
  have s072 : State 1152 basis072 w :=
    checkEntries_sound originalRow w hsource 1136 basis071 block071
      (hall 71 (by decide)) s071
  have s073 : State 1168 basis073 w :=
    checkEntries_sound originalRow w hsource 1152 basis072 block072
      (hall 72 (by decide)) s072
  have s074 : State 1184 basis074 w :=
    checkEntries_sound originalRow w hsource 1168 basis073 block073
      (hall 73 (by decide)) s073
  have s075 : State 1200 basis075 w :=
    checkEntries_sound originalRow w hsource 1184 basis074 block074
      (hall 74 (by decide)) s074
  have s076 : State 1216 basis076 w :=
    checkEntries_sound originalRow w hsource 1200 basis075 block075
      (hall 75 (by decide)) s075
  have s077 : State 1232 basis077 w :=
    checkEntries_sound originalRow w hsource 1216 basis076 block076
      (hall 76 (by decide)) s076
  have s078 : State 1248 basis078 w :=
    checkEntries_sound originalRow w hsource 1232 basis077 block077
      (hall 77 (by decide)) s077
  have s079 : State 1264 basis079 w :=
    checkEntries_sound originalRow w hsource 1248 basis078 block078
      (hall 78 (by decide)) s078
  have s080 : State 1280 basis080 w :=
    checkEntries_sound originalRow w hsource 1264 basis079 block079
      (hall 79 (by decide)) s079
  have s081 : State 1296 basis081 w :=
    checkEntries_sound originalRow w hsource 1280 basis080 block080
      (hall 80 (by decide)) s080
  have s082 : State 1312 basis082 w :=
    checkEntries_sound originalRow w hsource 1296 basis081 block081
      (hall 81 (by decide)) s081
  have s083 : State 1328 basis083 w :=
    checkEntries_sound originalRow w hsource 1312 basis082 block082
      (hall 82 (by decide)) s082
  have s084 : State 1344 basis084 w :=
    checkEntries_sound originalRow w hsource 1328 basis083 block083
      (hall 83 (by decide)) s083
  have s085 : State 1360 basis085 w :=
    checkEntries_sound originalRow w hsource 1344 basis084 block084
      (hall 84 (by decide)) s084
  have s086 : State 1376 basis086 w :=
    checkEntries_sound originalRow w hsource 1360 basis085 block085
      (hall 85 (by decide)) s085
  have s087 : State 1392 basis087 w :=
    checkEntries_sound originalRow w hsource 1376 basis086 block086
      (hall 86 (by decide)) s086
  have s088 : State 1408 basis088 w :=
    checkEntries_sound originalRow w hsource 1392 basis087 block087
      (hall 87 (by decide)) s087
  have s089 : State 1424 basis089 w :=
    checkEntries_sound originalRow w hsource 1408 basis088 block088
      (hall 88 (by decide)) s088
  have s090 : State 1440 basis090 w :=
    checkEntries_sound originalRow w hsource 1424 basis089 block089
      (hall 89 (by decide)) s089
  have s091 : State 1456 basis091 w :=
    checkEntries_sound originalRow w hsource 1440 basis090 block090
      (hall 90 (by decide)) s090
  have s092 : State 1472 basis092 w :=
    checkEntries_sound originalRow w hsource 1456 basis091 block091
      (hall 91 (by decide)) s091
  have s093 : State 1488 basis093 w :=
    checkEntries_sound originalRow w hsource 1472 basis092 block092
      (hall 92 (by decide)) s092
  have s094 : State 1504 basis094 w :=
    checkEntries_sound originalRow w hsource 1488 basis093 block093
      (hall 93 (by decide)) s093
  have s095 : State 1520 basis095 w :=
    checkEntries_sound originalRow w hsource 1504 basis094 block094
      (hall 94 (by decide)) s094
  have s096 : State 1536 basis096 w :=
    checkEntries_sound originalRow w hsource 1520 basis095 block095
      (hall 95 (by decide)) s095
  have s097 : State 1552 basis097 w :=
    checkEntries_sound originalRow w hsource 1536 basis096 block096
      (hall 96 (by decide)) s096
  have s098 : State 1568 basis098 w :=
    checkEntries_sound originalRow w hsource 1552 basis097 block097
      (hall 97 (by decide)) s097
  have s099 : State 1584 basis099 w :=
    checkEntries_sound originalRow w hsource 1568 basis098 block098
      (hall 98 (by decide)) s098
  have s100 : State 1600 basis100 w :=
    checkEntries_sound originalRow w hsource 1584 basis099 block099
      (hall 99 (by decide)) s099
  have s101 : State 1616 basis101 w :=
    checkEntries_sound originalRow w hsource 1600 basis100 block100
      (hall 100 (by decide)) s100
  have s102 : State 1632 basis102 w :=
    checkEntries_sound originalRow w hsource 1616 basis101 block101
      (hall 101 (by decide)) s101
  have s103 : State 1648 basis103 w :=
    checkEntries_sound originalRow w hsource 1632 basis102 block102
      (hall 102 (by decide)) s102
  have s104 : State 1664 basis104 w :=
    checkEntries_sound originalRow w hsource 1648 basis103 block103
      (hall 103 (by decide)) s103
  have s105 : State 1680 basis105 w :=
    checkEntries_sound originalRow w hsource 1664 basis104 block104
      (hall 104 (by decide)) s104
  have s106 : State 1696 basis106 w :=
    checkEntries_sound originalRow w hsource 1680 basis105 block105
      (hall 105 (by decide)) s105
  have s107 : State 1712 basis107 w :=
    checkEntries_sound originalRow w hsource 1696 basis106 block106
      (hall 106 (by decide)) s106
  have s108 : State 1728 basis108 w :=
    checkEntries_sound originalRow w hsource 1712 basis107 block107
      (hall 107 (by decide)) s107
  have s109 : State 1744 basis109 w :=
    checkEntries_sound originalRow w hsource 1728 basis108 block108
      (hall 108 (by decide)) s108
  have s110 : State 1760 basis110 w :=
    checkEntries_sound originalRow w hsource 1744 basis109 block109
      (hall 109 (by decide)) s109
  have s111 : State 1776 basis111 w :=
    checkEntries_sound originalRow w hsource 1760 basis110 block110
      (hall 110 (by decide)) s110
  have s112 : State 1792 basis112 w :=
    checkEntries_sound originalRow w hsource 1776 basis111 block111
      (hall 111 (by decide)) s111
  exact s112

/-- Apply elimination soundness to the actual matrix using its bounded checks. -/
theorem packedCompletion_isUnit_of_blockChecks (h : CompletionBlockChecks) :
    IsUnit packedCompletion := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : packedCompletion.mulVec (x-y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsource : ∀ i, i < 1792 → dot (originalRow i) (x-y) = 0 :=
    sourceRow_dot singularRows nucleusBits (x-y) hz
  exact state_complete basis112 (x-y) (completion_state_of_blockChecks h (x-y) hsource)

/-- The fixed packed completion is invertible, by all 1792 checked elimination pivots. -/
theorem packedCompletion_isUnit : IsUnit packedCompletion :=
  packedCompletion_isUnit_of_blockChecks completionBlockChecks

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate
