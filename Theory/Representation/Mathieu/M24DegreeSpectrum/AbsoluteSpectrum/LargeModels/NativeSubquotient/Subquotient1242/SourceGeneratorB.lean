module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.SourceGeneratorB.Batch23

/-!
# Literal sourceGeneratorB matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

private theorem rows : ∀ i : Fin 1474,
    combine ambientTransposeB embeddingTransposeRows[i.val]! = combine embeddingTransposeRows sourceTransposeB[i.val]! := by
  have hall : ∀ i : Fin (185*8),
      combine ambientTransposeB embeddingTransposeRows[i.val]! = combine embeddingTransposeRows sourceTransposeB[i.val]! := by
    apply forall_batches (blocks := 185) (size := 8) (by decide)
      (fun i => combine ambientTransposeB embeddingTransposeRows[i]! = combine embeddingTransposeRows sourceTransposeB[i]!)
    intro b j
    have h : checkEqualProducts ambientTransposeB embeddingTransposeRows
        ((embeddingTransposeRows.drop (b.val*8)).take 8) ((sourceTransposeB.drop (b.val*8)).take 8) = true := by
      fin_cases b
      · exact SourceGeneratorBChecks.block000
      · exact SourceGeneratorBChecks.block001
      · exact SourceGeneratorBChecks.block002
      · exact SourceGeneratorBChecks.block003
      · exact SourceGeneratorBChecks.block004
      · exact SourceGeneratorBChecks.block005
      · exact SourceGeneratorBChecks.block006
      · exact SourceGeneratorBChecks.block007
      · exact SourceGeneratorBChecks.block008
      · exact SourceGeneratorBChecks.block009
      · exact SourceGeneratorBChecks.block010
      · exact SourceGeneratorBChecks.block011
      · exact SourceGeneratorBChecks.block012
      · exact SourceGeneratorBChecks.block013
      · exact SourceGeneratorBChecks.block014
      · exact SourceGeneratorBChecks.block015
      · exact SourceGeneratorBChecks.block016
      · exact SourceGeneratorBChecks.block017
      · exact SourceGeneratorBChecks.block018
      · exact SourceGeneratorBChecks.block019
      · exact SourceGeneratorBChecks.block020
      · exact SourceGeneratorBChecks.block021
      · exact SourceGeneratorBChecks.block022
      · exact SourceGeneratorBChecks.block023
      · exact SourceGeneratorBChecks.block024
      · exact SourceGeneratorBChecks.block025
      · exact SourceGeneratorBChecks.block026
      · exact SourceGeneratorBChecks.block027
      · exact SourceGeneratorBChecks.block028
      · exact SourceGeneratorBChecks.block029
      · exact SourceGeneratorBChecks.block030
      · exact SourceGeneratorBChecks.block031
      · exact SourceGeneratorBChecks.block032
      · exact SourceGeneratorBChecks.block033
      · exact SourceGeneratorBChecks.block034
      · exact SourceGeneratorBChecks.block035
      · exact SourceGeneratorBChecks.block036
      · exact SourceGeneratorBChecks.block037
      · exact SourceGeneratorBChecks.block038
      · exact SourceGeneratorBChecks.block039
      · exact SourceGeneratorBChecks.block040
      · exact SourceGeneratorBChecks.block041
      · exact SourceGeneratorBChecks.block042
      · exact SourceGeneratorBChecks.block043
      · exact SourceGeneratorBChecks.block044
      · exact SourceGeneratorBChecks.block045
      · exact SourceGeneratorBChecks.block046
      · exact SourceGeneratorBChecks.block047
      · exact SourceGeneratorBChecks.block048
      · exact SourceGeneratorBChecks.block049
      · exact SourceGeneratorBChecks.block050
      · exact SourceGeneratorBChecks.block051
      · exact SourceGeneratorBChecks.block052
      · exact SourceGeneratorBChecks.block053
      · exact SourceGeneratorBChecks.block054
      · exact SourceGeneratorBChecks.block055
      · exact SourceGeneratorBChecks.block056
      · exact SourceGeneratorBChecks.block057
      · exact SourceGeneratorBChecks.block058
      · exact SourceGeneratorBChecks.block059
      · exact SourceGeneratorBChecks.block060
      · exact SourceGeneratorBChecks.block061
      · exact SourceGeneratorBChecks.block062
      · exact SourceGeneratorBChecks.block063
      · exact SourceGeneratorBChecks.block064
      · exact SourceGeneratorBChecks.block065
      · exact SourceGeneratorBChecks.block066
      · exact SourceGeneratorBChecks.block067
      · exact SourceGeneratorBChecks.block068
      · exact SourceGeneratorBChecks.block069
      · exact SourceGeneratorBChecks.block070
      · exact SourceGeneratorBChecks.block071
      · exact SourceGeneratorBChecks.block072
      · exact SourceGeneratorBChecks.block073
      · exact SourceGeneratorBChecks.block074
      · exact SourceGeneratorBChecks.block075
      · exact SourceGeneratorBChecks.block076
      · exact SourceGeneratorBChecks.block077
      · exact SourceGeneratorBChecks.block078
      · exact SourceGeneratorBChecks.block079
      · exact SourceGeneratorBChecks.block080
      · exact SourceGeneratorBChecks.block081
      · exact SourceGeneratorBChecks.block082
      · exact SourceGeneratorBChecks.block083
      · exact SourceGeneratorBChecks.block084
      · exact SourceGeneratorBChecks.block085
      · exact SourceGeneratorBChecks.block086
      · exact SourceGeneratorBChecks.block087
      · exact SourceGeneratorBChecks.block088
      · exact SourceGeneratorBChecks.block089
      · exact SourceGeneratorBChecks.block090
      · exact SourceGeneratorBChecks.block091
      · exact SourceGeneratorBChecks.block092
      · exact SourceGeneratorBChecks.block093
      · exact SourceGeneratorBChecks.block094
      · exact SourceGeneratorBChecks.block095
      · exact SourceGeneratorBChecks.block096
      · exact SourceGeneratorBChecks.block097
      · exact SourceGeneratorBChecks.block098
      · exact SourceGeneratorBChecks.block099
      · exact SourceGeneratorBChecks.block100
      · exact SourceGeneratorBChecks.block101
      · exact SourceGeneratorBChecks.block102
      · exact SourceGeneratorBChecks.block103
      · exact SourceGeneratorBChecks.block104
      · exact SourceGeneratorBChecks.block105
      · exact SourceGeneratorBChecks.block106
      · exact SourceGeneratorBChecks.block107
      · exact SourceGeneratorBChecks.block108
      · exact SourceGeneratorBChecks.block109
      · exact SourceGeneratorBChecks.block110
      · exact SourceGeneratorBChecks.block111
      · exact SourceGeneratorBChecks.block112
      · exact SourceGeneratorBChecks.block113
      · exact SourceGeneratorBChecks.block114
      · exact SourceGeneratorBChecks.block115
      · exact SourceGeneratorBChecks.block116
      · exact SourceGeneratorBChecks.block117
      · exact SourceGeneratorBChecks.block118
      · exact SourceGeneratorBChecks.block119
      · exact SourceGeneratorBChecks.block120
      · exact SourceGeneratorBChecks.block121
      · exact SourceGeneratorBChecks.block122
      · exact SourceGeneratorBChecks.block123
      · exact SourceGeneratorBChecks.block124
      · exact SourceGeneratorBChecks.block125
      · exact SourceGeneratorBChecks.block126
      · exact SourceGeneratorBChecks.block127
      · exact SourceGeneratorBChecks.block128
      · exact SourceGeneratorBChecks.block129
      · exact SourceGeneratorBChecks.block130
      · exact SourceGeneratorBChecks.block131
      · exact SourceGeneratorBChecks.block132
      · exact SourceGeneratorBChecks.block133
      · exact SourceGeneratorBChecks.block134
      · exact SourceGeneratorBChecks.block135
      · exact SourceGeneratorBChecks.block136
      · exact SourceGeneratorBChecks.block137
      · exact SourceGeneratorBChecks.block138
      · exact SourceGeneratorBChecks.block139
      · exact SourceGeneratorBChecks.block140
      · exact SourceGeneratorBChecks.block141
      · exact SourceGeneratorBChecks.block142
      · exact SourceGeneratorBChecks.block143
      · exact SourceGeneratorBChecks.block144
      · exact SourceGeneratorBChecks.block145
      · exact SourceGeneratorBChecks.block146
      · exact SourceGeneratorBChecks.block147
      · exact SourceGeneratorBChecks.block148
      · exact SourceGeneratorBChecks.block149
      · exact SourceGeneratorBChecks.block150
      · exact SourceGeneratorBChecks.block151
      · exact SourceGeneratorBChecks.block152
      · exact SourceGeneratorBChecks.block153
      · exact SourceGeneratorBChecks.block154
      · exact SourceGeneratorBChecks.block155
      · exact SourceGeneratorBChecks.block156
      · exact SourceGeneratorBChecks.block157
      · exact SourceGeneratorBChecks.block158
      · exact SourceGeneratorBChecks.block159
      · exact SourceGeneratorBChecks.block160
      · exact SourceGeneratorBChecks.block161
      · exact SourceGeneratorBChecks.block162
      · exact SourceGeneratorBChecks.block163
      · exact SourceGeneratorBChecks.block164
      · exact SourceGeneratorBChecks.block165
      · exact SourceGeneratorBChecks.block166
      · exact SourceGeneratorBChecks.block167
      · exact SourceGeneratorBChecks.block168
      · exact SourceGeneratorBChecks.block169
      · exact SourceGeneratorBChecks.block170
      · exact SourceGeneratorBChecks.block171
      · exact SourceGeneratorBChecks.block172
      · exact SourceGeneratorBChecks.block173
      · exact SourceGeneratorBChecks.block174
      · exact SourceGeneratorBChecks.block175
      · exact SourceGeneratorBChecks.block176
      · exact SourceGeneratorBChecks.block177
      · exact SourceGeneratorBChecks.block178
      · exact SourceGeneratorBChecks.block179
      · exact SourceGeneratorBChecks.block180
      · exact SourceGeneratorBChecks.block181
      · exact SourceGeneratorBChecks.block182
      · exact SourceGeneratorBChecks.block183
      · exact SourceGeneratorBChecks.block184
    have he := checkEqualProducts_sound _ _ _ _ h j.val
    simpa only [chunk_entry _ _ _ _ j.isLt] using he
  intro i
  exact hall ⟨i.val, by omega⟩

/-- The saved intertwiner in the literal rectangular matrix coordinates. -/
theorem sourceGeneratorB :
    matrix 1474 1936 embeddingTransposeRows * matrix 1936 1936 ambientTransposeB =
      matrix 1474 1474 sourceTransposeB * matrix 1474 1936 embeddingTransposeRows :=
  matrix_equal_products_of_rows _ _ _ _ (by decide +kernel) (by decide +kernel) rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
