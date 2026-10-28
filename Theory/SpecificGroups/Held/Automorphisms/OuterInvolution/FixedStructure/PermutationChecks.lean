module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.PermutationChecks.Blocks
public import Mathlib.Tactic.FinCases

/-!
# Identification of the tabulated Bray permutation

The blocks cover every letter, so the fast permutation is exactly the word
in the literal Held carrier. Subsequent relation checks can use this table
without repeatedly expanding the long word.
Source: ATLAS HeG1-p2058B0; the checked blocks in `PermutationChecks.Blocks`.
-/

namespace Held.OuterInvolution.FixedStructure

private theorem allPointsByBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 129, ∀ r : Fin 16,
      P ⟨(q.val * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) : ∀ x, P x := by
  intro x
  have hx := h ⟨x.val / 16, by omega⟩ ⟨x.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : x.val / 16 * 16 + x.val % 16 = x.val := by omega
  simpa only [he, Nat.mod_eq_of_lt x.isLt] using hx

/-- The fast permutation is exactly the word in the literal Held carrier. -/
public theorem bray_representation : representation bray = brayPermutation := by
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact PermutationCertificate.bray_eq_0
  · exact PermutationCertificate.bray_eq_1
  · exact PermutationCertificate.bray_eq_2
  · exact PermutationCertificate.bray_eq_3
  · exact PermutationCertificate.bray_eq_4
  · exact PermutationCertificate.bray_eq_5
  · exact PermutationCertificate.bray_eq_6
  · exact PermutationCertificate.bray_eq_7
  · exact PermutationCertificate.bray_eq_8
  · exact PermutationCertificate.bray_eq_9
  · exact PermutationCertificate.bray_eq_10
  · exact PermutationCertificate.bray_eq_11
  · exact PermutationCertificate.bray_eq_12
  · exact PermutationCertificate.bray_eq_13
  · exact PermutationCertificate.bray_eq_14
  · exact PermutationCertificate.bray_eq_15
  · exact PermutationCertificate.bray_eq_16
  · exact PermutationCertificate.bray_eq_17
  · exact PermutationCertificate.bray_eq_18
  · exact PermutationCertificate.bray_eq_19
  · exact PermutationCertificate.bray_eq_20
  · exact PermutationCertificate.bray_eq_21
  · exact PermutationCertificate.bray_eq_22
  · exact PermutationCertificate.bray_eq_23
  · exact PermutationCertificate.bray_eq_24
  · exact PermutationCertificate.bray_eq_25
  · exact PermutationCertificate.bray_eq_26
  · exact PermutationCertificate.bray_eq_27
  · exact PermutationCertificate.bray_eq_28
  · exact PermutationCertificate.bray_eq_29
  · exact PermutationCertificate.bray_eq_30
  · exact PermutationCertificate.bray_eq_31
  · exact PermutationCertificate.bray_eq_32
  · exact PermutationCertificate.bray_eq_33
  · exact PermutationCertificate.bray_eq_34
  · exact PermutationCertificate.bray_eq_35
  · exact PermutationCertificate.bray_eq_36
  · exact PermutationCertificate.bray_eq_37
  · exact PermutationCertificate.bray_eq_38
  · exact PermutationCertificate.bray_eq_39
  · exact PermutationCertificate.bray_eq_40
  · exact PermutationCertificate.bray_eq_41
  · exact PermutationCertificate.bray_eq_42
  · exact PermutationCertificate.bray_eq_43
  · exact PermutationCertificate.bray_eq_44
  · exact PermutationCertificate.bray_eq_45
  · exact PermutationCertificate.bray_eq_46
  · exact PermutationCertificate.bray_eq_47
  · exact PermutationCertificate.bray_eq_48
  · exact PermutationCertificate.bray_eq_49
  · exact PermutationCertificate.bray_eq_50
  · exact PermutationCertificate.bray_eq_51
  · exact PermutationCertificate.bray_eq_52
  · exact PermutationCertificate.bray_eq_53
  · exact PermutationCertificate.bray_eq_54
  · exact PermutationCertificate.bray_eq_55
  · exact PermutationCertificate.bray_eq_56
  · exact PermutationCertificate.bray_eq_57
  · exact PermutationCertificate.bray_eq_58
  · exact PermutationCertificate.bray_eq_59
  · exact PermutationCertificate.bray_eq_60
  · exact PermutationCertificate.bray_eq_61
  · exact PermutationCertificate.bray_eq_62
  · exact PermutationCertificate.bray_eq_63
  · exact PermutationCertificate.bray_eq_64
  · exact PermutationCertificate.bray_eq_65
  · exact PermutationCertificate.bray_eq_66
  · exact PermutationCertificate.bray_eq_67
  · exact PermutationCertificate.bray_eq_68
  · exact PermutationCertificate.bray_eq_69
  · exact PermutationCertificate.bray_eq_70
  · exact PermutationCertificate.bray_eq_71
  · exact PermutationCertificate.bray_eq_72
  · exact PermutationCertificate.bray_eq_73
  · exact PermutationCertificate.bray_eq_74
  · exact PermutationCertificate.bray_eq_75
  · exact PermutationCertificate.bray_eq_76
  · exact PermutationCertificate.bray_eq_77
  · exact PermutationCertificate.bray_eq_78
  · exact PermutationCertificate.bray_eq_79
  · exact PermutationCertificate.bray_eq_80
  · exact PermutationCertificate.bray_eq_81
  · exact PermutationCertificate.bray_eq_82
  · exact PermutationCertificate.bray_eq_83
  · exact PermutationCertificate.bray_eq_84
  · exact PermutationCertificate.bray_eq_85
  · exact PermutationCertificate.bray_eq_86
  · exact PermutationCertificate.bray_eq_87
  · exact PermutationCertificate.bray_eq_88
  · exact PermutationCertificate.bray_eq_89
  · exact PermutationCertificate.bray_eq_90
  · exact PermutationCertificate.bray_eq_91
  · exact PermutationCertificate.bray_eq_92
  · exact PermutationCertificate.bray_eq_93
  · exact PermutationCertificate.bray_eq_94
  · exact PermutationCertificate.bray_eq_95
  · exact PermutationCertificate.bray_eq_96
  · exact PermutationCertificate.bray_eq_97
  · exact PermutationCertificate.bray_eq_98
  · exact PermutationCertificate.bray_eq_99
  · exact PermutationCertificate.bray_eq_100
  · exact PermutationCertificate.bray_eq_101
  · exact PermutationCertificate.bray_eq_102
  · exact PermutationCertificate.bray_eq_103
  · exact PermutationCertificate.bray_eq_104
  · exact PermutationCertificate.bray_eq_105
  · exact PermutationCertificate.bray_eq_106
  · exact PermutationCertificate.bray_eq_107
  · exact PermutationCertificate.bray_eq_108
  · exact PermutationCertificate.bray_eq_109
  · exact PermutationCertificate.bray_eq_110
  · exact PermutationCertificate.bray_eq_111
  · exact PermutationCertificate.bray_eq_112
  · exact PermutationCertificate.bray_eq_113
  · exact PermutationCertificate.bray_eq_114
  · exact PermutationCertificate.bray_eq_115
  · exact PermutationCertificate.bray_eq_116
  · exact PermutationCertificate.bray_eq_117
  · exact PermutationCertificate.bray_eq_118
  · exact PermutationCertificate.bray_eq_119
  · exact PermutationCertificate.bray_eq_120
  · exact PermutationCertificate.bray_eq_121
  · exact PermutationCertificate.bray_eq_122
  · exact PermutationCertificate.bray_eq_123
  · exact PermutationCertificate.bray_eq_124
  · exact PermutationCertificate.bray_eq_125
  · exact PermutationCertificate.bray_eq_126
  · exact PermutationCertificate.bray_eq_127
  · exact PermutationCertificate.bray_eq_128

end Held.OuterInvolution.FixedStructure
