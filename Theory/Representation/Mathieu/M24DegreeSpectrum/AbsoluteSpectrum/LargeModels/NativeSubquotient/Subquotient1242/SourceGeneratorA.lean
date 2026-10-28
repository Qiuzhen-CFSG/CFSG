module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.SourceGeneratorA.Batch23

/-!
# Literal sourceGeneratorA matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

private theorem rows : ∀ i : Fin 1474,
    combine ambientTransposeA embeddingTransposeRows[i.val]! = combine embeddingTransposeRows sourceTransposeA[i.val]! := by
  have hall : ∀ i : Fin (185*8),
      combine ambientTransposeA embeddingTransposeRows[i.val]! = combine embeddingTransposeRows sourceTransposeA[i.val]! := by
    apply forall_batches (blocks := 185) (size := 8) (by decide)
      (fun i => combine ambientTransposeA embeddingTransposeRows[i]! = combine embeddingTransposeRows sourceTransposeA[i]!)
    intro b j
    have h : checkEqualProducts ambientTransposeA embeddingTransposeRows
        ((embeddingTransposeRows.drop (b.val*8)).take 8) ((sourceTransposeA.drop (b.val*8)).take 8) = true := by
      fin_cases b
      · exact SourceGeneratorAChecks.block000
      · exact SourceGeneratorAChecks.block001
      · exact SourceGeneratorAChecks.block002
      · exact SourceGeneratorAChecks.block003
      · exact SourceGeneratorAChecks.block004
      · exact SourceGeneratorAChecks.block005
      · exact SourceGeneratorAChecks.block006
      · exact SourceGeneratorAChecks.block007
      · exact SourceGeneratorAChecks.block008
      · exact SourceGeneratorAChecks.block009
      · exact SourceGeneratorAChecks.block010
      · exact SourceGeneratorAChecks.block011
      · exact SourceGeneratorAChecks.block012
      · exact SourceGeneratorAChecks.block013
      · exact SourceGeneratorAChecks.block014
      · exact SourceGeneratorAChecks.block015
      · exact SourceGeneratorAChecks.block016
      · exact SourceGeneratorAChecks.block017
      · exact SourceGeneratorAChecks.block018
      · exact SourceGeneratorAChecks.block019
      · exact SourceGeneratorAChecks.block020
      · exact SourceGeneratorAChecks.block021
      · exact SourceGeneratorAChecks.block022
      · exact SourceGeneratorAChecks.block023
      · exact SourceGeneratorAChecks.block024
      · exact SourceGeneratorAChecks.block025
      · exact SourceGeneratorAChecks.block026
      · exact SourceGeneratorAChecks.block027
      · exact SourceGeneratorAChecks.block028
      · exact SourceGeneratorAChecks.block029
      · exact SourceGeneratorAChecks.block030
      · exact SourceGeneratorAChecks.block031
      · exact SourceGeneratorAChecks.block032
      · exact SourceGeneratorAChecks.block033
      · exact SourceGeneratorAChecks.block034
      · exact SourceGeneratorAChecks.block035
      · exact SourceGeneratorAChecks.block036
      · exact SourceGeneratorAChecks.block037
      · exact SourceGeneratorAChecks.block038
      · exact SourceGeneratorAChecks.block039
      · exact SourceGeneratorAChecks.block040
      · exact SourceGeneratorAChecks.block041
      · exact SourceGeneratorAChecks.block042
      · exact SourceGeneratorAChecks.block043
      · exact SourceGeneratorAChecks.block044
      · exact SourceGeneratorAChecks.block045
      · exact SourceGeneratorAChecks.block046
      · exact SourceGeneratorAChecks.block047
      · exact SourceGeneratorAChecks.block048
      · exact SourceGeneratorAChecks.block049
      · exact SourceGeneratorAChecks.block050
      · exact SourceGeneratorAChecks.block051
      · exact SourceGeneratorAChecks.block052
      · exact SourceGeneratorAChecks.block053
      · exact SourceGeneratorAChecks.block054
      · exact SourceGeneratorAChecks.block055
      · exact SourceGeneratorAChecks.block056
      · exact SourceGeneratorAChecks.block057
      · exact SourceGeneratorAChecks.block058
      · exact SourceGeneratorAChecks.block059
      · exact SourceGeneratorAChecks.block060
      · exact SourceGeneratorAChecks.block061
      · exact SourceGeneratorAChecks.block062
      · exact SourceGeneratorAChecks.block063
      · exact SourceGeneratorAChecks.block064
      · exact SourceGeneratorAChecks.block065
      · exact SourceGeneratorAChecks.block066
      · exact SourceGeneratorAChecks.block067
      · exact SourceGeneratorAChecks.block068
      · exact SourceGeneratorAChecks.block069
      · exact SourceGeneratorAChecks.block070
      · exact SourceGeneratorAChecks.block071
      · exact SourceGeneratorAChecks.block072
      · exact SourceGeneratorAChecks.block073
      · exact SourceGeneratorAChecks.block074
      · exact SourceGeneratorAChecks.block075
      · exact SourceGeneratorAChecks.block076
      · exact SourceGeneratorAChecks.block077
      · exact SourceGeneratorAChecks.block078
      · exact SourceGeneratorAChecks.block079
      · exact SourceGeneratorAChecks.block080
      · exact SourceGeneratorAChecks.block081
      · exact SourceGeneratorAChecks.block082
      · exact SourceGeneratorAChecks.block083
      · exact SourceGeneratorAChecks.block084
      · exact SourceGeneratorAChecks.block085
      · exact SourceGeneratorAChecks.block086
      · exact SourceGeneratorAChecks.block087
      · exact SourceGeneratorAChecks.block088
      · exact SourceGeneratorAChecks.block089
      · exact SourceGeneratorAChecks.block090
      · exact SourceGeneratorAChecks.block091
      · exact SourceGeneratorAChecks.block092
      · exact SourceGeneratorAChecks.block093
      · exact SourceGeneratorAChecks.block094
      · exact SourceGeneratorAChecks.block095
      · exact SourceGeneratorAChecks.block096
      · exact SourceGeneratorAChecks.block097
      · exact SourceGeneratorAChecks.block098
      · exact SourceGeneratorAChecks.block099
      · exact SourceGeneratorAChecks.block100
      · exact SourceGeneratorAChecks.block101
      · exact SourceGeneratorAChecks.block102
      · exact SourceGeneratorAChecks.block103
      · exact SourceGeneratorAChecks.block104
      · exact SourceGeneratorAChecks.block105
      · exact SourceGeneratorAChecks.block106
      · exact SourceGeneratorAChecks.block107
      · exact SourceGeneratorAChecks.block108
      · exact SourceGeneratorAChecks.block109
      · exact SourceGeneratorAChecks.block110
      · exact SourceGeneratorAChecks.block111
      · exact SourceGeneratorAChecks.block112
      · exact SourceGeneratorAChecks.block113
      · exact SourceGeneratorAChecks.block114
      · exact SourceGeneratorAChecks.block115
      · exact SourceGeneratorAChecks.block116
      · exact SourceGeneratorAChecks.block117
      · exact SourceGeneratorAChecks.block118
      · exact SourceGeneratorAChecks.block119
      · exact SourceGeneratorAChecks.block120
      · exact SourceGeneratorAChecks.block121
      · exact SourceGeneratorAChecks.block122
      · exact SourceGeneratorAChecks.block123
      · exact SourceGeneratorAChecks.block124
      · exact SourceGeneratorAChecks.block125
      · exact SourceGeneratorAChecks.block126
      · exact SourceGeneratorAChecks.block127
      · exact SourceGeneratorAChecks.block128
      · exact SourceGeneratorAChecks.block129
      · exact SourceGeneratorAChecks.block130
      · exact SourceGeneratorAChecks.block131
      · exact SourceGeneratorAChecks.block132
      · exact SourceGeneratorAChecks.block133
      · exact SourceGeneratorAChecks.block134
      · exact SourceGeneratorAChecks.block135
      · exact SourceGeneratorAChecks.block136
      · exact SourceGeneratorAChecks.block137
      · exact SourceGeneratorAChecks.block138
      · exact SourceGeneratorAChecks.block139
      · exact SourceGeneratorAChecks.block140
      · exact SourceGeneratorAChecks.block141
      · exact SourceGeneratorAChecks.block142
      · exact SourceGeneratorAChecks.block143
      · exact SourceGeneratorAChecks.block144
      · exact SourceGeneratorAChecks.block145
      · exact SourceGeneratorAChecks.block146
      · exact SourceGeneratorAChecks.block147
      · exact SourceGeneratorAChecks.block148
      · exact SourceGeneratorAChecks.block149
      · exact SourceGeneratorAChecks.block150
      · exact SourceGeneratorAChecks.block151
      · exact SourceGeneratorAChecks.block152
      · exact SourceGeneratorAChecks.block153
      · exact SourceGeneratorAChecks.block154
      · exact SourceGeneratorAChecks.block155
      · exact SourceGeneratorAChecks.block156
      · exact SourceGeneratorAChecks.block157
      · exact SourceGeneratorAChecks.block158
      · exact SourceGeneratorAChecks.block159
      · exact SourceGeneratorAChecks.block160
      · exact SourceGeneratorAChecks.block161
      · exact SourceGeneratorAChecks.block162
      · exact SourceGeneratorAChecks.block163
      · exact SourceGeneratorAChecks.block164
      · exact SourceGeneratorAChecks.block165
      · exact SourceGeneratorAChecks.block166
      · exact SourceGeneratorAChecks.block167
      · exact SourceGeneratorAChecks.block168
      · exact SourceGeneratorAChecks.block169
      · exact SourceGeneratorAChecks.block170
      · exact SourceGeneratorAChecks.block171
      · exact SourceGeneratorAChecks.block172
      · exact SourceGeneratorAChecks.block173
      · exact SourceGeneratorAChecks.block174
      · exact SourceGeneratorAChecks.block175
      · exact SourceGeneratorAChecks.block176
      · exact SourceGeneratorAChecks.block177
      · exact SourceGeneratorAChecks.block178
      · exact SourceGeneratorAChecks.block179
      · exact SourceGeneratorAChecks.block180
      · exact SourceGeneratorAChecks.block181
      · exact SourceGeneratorAChecks.block182
      · exact SourceGeneratorAChecks.block183
      · exact SourceGeneratorAChecks.block184
    have he := checkEqualProducts_sound _ _ _ _ h j.val
    simpa only [chunk_entry _ _ _ _ j.isLt] using he
  intro i
  exact hall ⟨i.val, by omega⟩

/-- The saved intertwiner in the literal rectangular matrix coordinates. -/
theorem sourceGeneratorA :
    matrix 1474 1936 embeddingTransposeRows * matrix 1936 1936 ambientTransposeA =
      matrix 1474 1474 sourceTransposeA * matrix 1474 1936 embeddingTransposeRows :=
  matrix_equal_products_of_rows _ _ _ _ (by decide +kernel) (by decide +kernel) rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
