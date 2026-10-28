module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Elementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Exceptional
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery00
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery01
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery02
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery03
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery04
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery05
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery06
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery07
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery08
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery09
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery10
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery11
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery12
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery13
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Recovery14
import Mathlib.Tactic.FinCases

/-!
# Conjugate-pair generation and the exceptional overgroup

Inside the auxiliary certified HS point stabilizer C, let P be the specified
cyclic subgroup of order eleven and L = P ∨ r₁ P r₁⁻¹. The normalizer candidate
N lies in L, the index [C:L] is greater than 100, and each of the 150 specified
representatives either belongs to L or its conjugate of P generates C with P.

The proof consists of explicit recovery words and an invariant 11-point set.
The latter has 101 provably distinct translates, giving the required index
bound without computing |L|. Every finite identity is checked by Lean's kernel.
The comparison with the actual HS stabilizer and double-coset coverage are
separate results; no such premise is used here.
Source context: GLS3 Table 5.3m, printed p.274; Aschbacher–Smith printed p.510.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex
open Subgroup GenerationCertificate

/-- The explicit normalizer candidate is contained in the exceptional overgroup. -/
theorem normalizerCandidate_le_exceptionalSubgroup :
    normalizerCandidate ≤ exceptionalSubgroup := by
  apply sup_le le_sup_left
  apply zpowers_le.mpr
  rw [← normalizer_word]
  exact pairWord_mem 1 _

/-- The exceptional overgroup has index greater than 100, with index taken in C. -/
theorem exceptionalSubgroup_index_gt : 100 < exceptionalSubgroup.index :=
  lt_of_lt_of_le (by decide : 100 < 101) exceptional_index_lower_bound

/-- Every specified representative is exceptional or its conjugate pair generates C. -/
theorem representative_mem_or_pair_eq_top (i : Fin 150) :
    representative i ∈ exceptionalSubgroup ∨
      primeSubgroup ⊔ primeSubgroup.map (MulAut.conj (representative i)).toMonoidHom = ⊤ := by
  fin_cases i
  · exact Or.inl exceptionalSubgroup.one_mem
  · apply Or.inl
    change representative 1 ∈ exceptionalSubgroup
    rw [← representative_one_word]
    exact pairWord_mem 1 _
  · exact Or.inr recover_002
  · exact Or.inr recover_003
  · exact Or.inr recover_004
  · exact Or.inr recover_005
  · exact Or.inr recover_006
  · exact Or.inr recover_007
  · exact Or.inr recover_008
  · exact Or.inr recover_009
  · exact Or.inr recover_010
  · exact Or.inr recover_011
  · exact Or.inr recover_012
  · exact Or.inr recover_013
  · exact Or.inr recover_014
  · exact Or.inr recover_015
  · exact Or.inr recover_016
  · exact Or.inr recover_017
  · exact Or.inr recover_018
  · exact Or.inr recover_019
  · exact Or.inr recover_020
  · exact Or.inr recover_021
  · exact Or.inr recover_022
  · exact Or.inr recover_023
  · exact Or.inr recover_024
  · exact Or.inr recover_025
  · exact Or.inr recover_026
  · exact Or.inr recover_027
  · exact Or.inr recover_028
  · exact Or.inr recover_029
  · exact Or.inr recover_030
  · exact Or.inr recover_031
  · exact Or.inr recover_032
  · exact Or.inr recover_033
  · exact Or.inr recover_034
  · exact Or.inr recover_035
  · exact Or.inr recover_036
  · exact Or.inr recover_037
  · exact Or.inr recover_038
  · exact Or.inr recover_039
  · exact Or.inr recover_040
  · exact Or.inr recover_041
  · exact Or.inr recover_042
  · exact Or.inr recover_043
  · exact Or.inr recover_044
  · exact Or.inr recover_045
  · exact Or.inr recover_046
  · exact Or.inr recover_047
  · exact Or.inr recover_048
  · exact Or.inr recover_049
  · exact Or.inr recover_050
  · exact Or.inr recover_051
  · exact Or.inr recover_052
  · exact Or.inr recover_053
  · exact Or.inr recover_054
  · exact Or.inr recover_055
  · exact Or.inr recover_056
  · exact Or.inr recover_057
  · exact Or.inr recover_058
  · exact Or.inr recover_059
  · exact Or.inr recover_060
  · exact Or.inr recover_061
  · exact Or.inr recover_062
  · exact Or.inr recover_063
  · exact Or.inr recover_064
  · exact Or.inr recover_065
  · exact Or.inr recover_066
  · exact Or.inr recover_067
  · exact Or.inr recover_068
  · exact Or.inr recover_069
  · exact Or.inr recover_070
  · exact Or.inr recover_071
  · exact Or.inr recover_072
  · exact Or.inr recover_073
  · exact Or.inr recover_074
  · exact Or.inr recover_075
  · exact Or.inr recover_076
  · exact Or.inr recover_077
  · exact Or.inr recover_078
  · exact Or.inr recover_079
  · exact Or.inr recover_080
  · exact Or.inr recover_081
  · exact Or.inr recover_082
  · exact Or.inr recover_083
  · exact Or.inr recover_084
  · exact Or.inr recover_085
  · exact Or.inr recover_086
  · exact Or.inr recover_087
  · exact Or.inr recover_088
  · exact Or.inr recover_089
  · exact Or.inr recover_090
  · exact Or.inr recover_091
  · exact Or.inr recover_092
  · exact Or.inr recover_093
  · exact Or.inr recover_094
  · exact Or.inr recover_095
  · exact Or.inr recover_096
  · exact Or.inr recover_097
  · exact Or.inr recover_098
  · exact Or.inr recover_099
  · exact Or.inr recover_100
  · exact Or.inr recover_101
  · exact Or.inr recover_102
  · exact Or.inr recover_103
  · exact Or.inr recover_104
  · exact Or.inr recover_105
  · exact Or.inr recover_106
  · exact Or.inr recover_107
  · exact Or.inr recover_108
  · exact Or.inr recover_109
  · exact Or.inr recover_110
  · exact Or.inr recover_111
  · exact Or.inr recover_112
  · exact Or.inr recover_113
  · exact Or.inr recover_114
  · exact Or.inr recover_115
  · exact Or.inr recover_116
  · exact Or.inr recover_117
  · exact Or.inr recover_118
  · exact Or.inr recover_119
  · exact Or.inr recover_120
  · exact Or.inr recover_121
  · exact Or.inr recover_122
  · exact Or.inr recover_123
  · exact Or.inr recover_124
  · exact Or.inr recover_125
  · exact Or.inr recover_126
  · exact Or.inr recover_127
  · exact Or.inr recover_128
  · exact Or.inr recover_129
  · exact Or.inr recover_130
  · exact Or.inr recover_131
  · exact Or.inr recover_132
  · exact Or.inr recover_133
  · exact Or.inr recover_134
  · exact Or.inr recover_135
  · exact Or.inr recover_136
  · exact Or.inr recover_137
  · exact Or.inr recover_138
  · exact Or.inr recover_139
  · exact Or.inr recover_140
  · exact Or.inr recover_141
  · exact Or.inr recover_142
  · exact Or.inr recover_143
  · exact Or.inr recover_144
  · exact Or.inr recover_145
  · exact Or.inr recover_146
  · exact Or.inr recover_147
  · exact Or.inr recover_148
  · exact Or.inr recover_149

end Sporadic.LeechRelated.HS.SmallIndex
