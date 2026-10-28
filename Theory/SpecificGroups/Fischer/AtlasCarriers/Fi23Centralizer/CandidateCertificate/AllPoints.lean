module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range00
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range01
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range02
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range03
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range04
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range05
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range06
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range07
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range08
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range09
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range10
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range12
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range13
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range14
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Range15

/-!
# Universal numerical checks for the Fi23 candidate

The 128 balanced certificates cover all 31671 ATLAS letters. Their Boolean
conjunction retains every premise required by the permutation comparison.
Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
private theorem ranges (b : Fin 128) : checkRange pointCheck 8 (256 * b.val) = true := by
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact range0
  · exact range1
  · exact range2
  · exact range3
  · exact range4
  · exact range5
  · exact range6
  · exact range7
  · exact range8
  · exact range9
  · exact range10
  · exact range11
  · exact range12
  · exact range13
  · exact range14
  · exact range15
  · exact range16
  · exact range17
  · exact range18
  · exact range19
  · exact range20
  · exact range21
  · exact range22
  · exact range23
  · exact range24
  · exact range25
  · exact range26
  · exact range27
  · exact range28
  · exact range29
  · exact range30
  · exact range31
  · exact range32
  · exact range33
  · exact range34
  · exact range35
  · exact range36
  · exact range37
  · exact range38
  · exact range39
  · exact range40
  · exact range41
  · exact range42
  · exact range43
  · exact range44
  · exact range45
  · exact range46
  · exact range47
  · exact range48
  · exact range49
  · exact range50
  · exact range51
  · exact range52
  · exact range53
  · exact range54
  · exact range55
  · exact range56
  · exact range57
  · exact range58
  · exact range59
  · exact range60
  · exact range61
  · exact range62
  · exact range63
  · exact range64
  · exact range65
  · exact range66
  · exact range67
  · exact range68
  · exact range69
  · exact range70
  · exact range71
  · exact range72
  · exact range73
  · exact range74
  · exact range75
  · exact range76
  · exact range77
  · exact range78
  · exact range79
  · exact range80
  · exact range81
  · exact range82
  · exact range83
  · exact range84
  · exact range85
  · exact range86
  · exact range87
  · exact range88
  · exact range89
  · exact range90
  · exact range91
  · exact range92
  · exact range93
  · exact range94
  · exact range95
  · exact range96
  · exact range97
  · exact range98
  · exact range99
  · exact range100
  · exact range101
  · exact range102
  · exact range103
  · exact range104
  · exact range105
  · exact range106
  · exact range107
  · exact range108
  · exact range109
  · exact range110
  · exact range111
  · exact range112
  · exact range113
  · exact range114
  · exact range115
  · exact range116
  · exact range117
  · exact range118
  · exact range119
  · exact range120
  · exact range121
  · exact range122
  · exact range123
  · exact range124
  · exact range125
  · exact range126
  · exact range127

theorem pointCheck_all (x : Fin 31671) : pointCheck x.val = true := by
  have hb : x.val / 256 < 128 := by omega
  exact (checkRange_spec pointCheck 8 (256 * (x.val / 256))).mp
    (ranges ⟨x.val / 256, hb⟩) x.val (by omega) (by norm_num; omega)

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
