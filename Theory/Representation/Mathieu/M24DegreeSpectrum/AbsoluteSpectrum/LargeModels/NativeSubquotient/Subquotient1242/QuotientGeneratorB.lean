module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorB.Batch23

/-!
# Literal quotientGeneratorB matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

private theorem rows : ∀ i : Fin 1474,
    combine quotientTransposeRows sourceTransposeB[i.val]! = combine targetB quotientTransposeRows[i.val]! := by
  have hall : ∀ i : Fin (185*8),
      combine quotientTransposeRows sourceTransposeB[i.val]! = combine targetB quotientTransposeRows[i.val]! := by
    apply forall_batches (blocks := 185) (size := 8) (by decide)
      (fun i => combine quotientTransposeRows sourceTransposeB[i]! = combine targetB quotientTransposeRows[i]!)
    intro b j
    have h : checkEqualProducts quotientTransposeRows targetB
        ((sourceTransposeB.drop (b.val*8)).take 8) ((quotientTransposeRows.drop (b.val*8)).take 8) = true := by
      fin_cases b
      · exact QuotientGeneratorBChecks.block000
      · exact QuotientGeneratorBChecks.block001
      · exact QuotientGeneratorBChecks.block002
      · exact QuotientGeneratorBChecks.block003
      · exact QuotientGeneratorBChecks.block004
      · exact QuotientGeneratorBChecks.block005
      · exact QuotientGeneratorBChecks.block006
      · exact QuotientGeneratorBChecks.block007
      · exact QuotientGeneratorBChecks.block008
      · exact QuotientGeneratorBChecks.block009
      · exact QuotientGeneratorBChecks.block010
      · exact QuotientGeneratorBChecks.block011
      · exact QuotientGeneratorBChecks.block012
      · exact QuotientGeneratorBChecks.block013
      · exact QuotientGeneratorBChecks.block014
      · exact QuotientGeneratorBChecks.block015
      · exact QuotientGeneratorBChecks.block016
      · exact QuotientGeneratorBChecks.block017
      · exact QuotientGeneratorBChecks.block018
      · exact QuotientGeneratorBChecks.block019
      · exact QuotientGeneratorBChecks.block020
      · exact QuotientGeneratorBChecks.block021
      · exact QuotientGeneratorBChecks.block022
      · exact QuotientGeneratorBChecks.block023
      · exact QuotientGeneratorBChecks.block024
      · exact QuotientGeneratorBChecks.block025
      · exact QuotientGeneratorBChecks.block026
      · exact QuotientGeneratorBChecks.block027
      · exact QuotientGeneratorBChecks.block028
      · exact QuotientGeneratorBChecks.block029
      · exact QuotientGeneratorBChecks.block030
      · exact QuotientGeneratorBChecks.block031
      · exact QuotientGeneratorBChecks.block032
      · exact QuotientGeneratorBChecks.block033
      · exact QuotientGeneratorBChecks.block034
      · exact QuotientGeneratorBChecks.block035
      · exact QuotientGeneratorBChecks.block036
      · exact QuotientGeneratorBChecks.block037
      · exact QuotientGeneratorBChecks.block038
      · exact QuotientGeneratorBChecks.block039
      · exact QuotientGeneratorBChecks.block040
      · exact QuotientGeneratorBChecks.block041
      · exact QuotientGeneratorBChecks.block042
      · exact QuotientGeneratorBChecks.block043
      · exact QuotientGeneratorBChecks.block044
      · exact QuotientGeneratorBChecks.block045
      · exact QuotientGeneratorBChecks.block046
      · exact QuotientGeneratorBChecks.block047
      · exact QuotientGeneratorBChecks.block048
      · exact QuotientGeneratorBChecks.block049
      · exact QuotientGeneratorBChecks.block050
      · exact QuotientGeneratorBChecks.block051
      · exact QuotientGeneratorBChecks.block052
      · exact QuotientGeneratorBChecks.block053
      · exact QuotientGeneratorBChecks.block054
      · exact QuotientGeneratorBChecks.block055
      · exact QuotientGeneratorBChecks.block056
      · exact QuotientGeneratorBChecks.block057
      · exact QuotientGeneratorBChecks.block058
      · exact QuotientGeneratorBChecks.block059
      · exact QuotientGeneratorBChecks.block060
      · exact QuotientGeneratorBChecks.block061
      · exact QuotientGeneratorBChecks.block062
      · exact QuotientGeneratorBChecks.block063
      · exact QuotientGeneratorBChecks.block064
      · exact QuotientGeneratorBChecks.block065
      · exact QuotientGeneratorBChecks.block066
      · exact QuotientGeneratorBChecks.block067
      · exact QuotientGeneratorBChecks.block068
      · exact QuotientGeneratorBChecks.block069
      · exact QuotientGeneratorBChecks.block070
      · exact QuotientGeneratorBChecks.block071
      · exact QuotientGeneratorBChecks.block072
      · exact QuotientGeneratorBChecks.block073
      · exact QuotientGeneratorBChecks.block074
      · exact QuotientGeneratorBChecks.block075
      · exact QuotientGeneratorBChecks.block076
      · exact QuotientGeneratorBChecks.block077
      · exact QuotientGeneratorBChecks.block078
      · exact QuotientGeneratorBChecks.block079
      · exact QuotientGeneratorBChecks.block080
      · exact QuotientGeneratorBChecks.block081
      · exact QuotientGeneratorBChecks.block082
      · exact QuotientGeneratorBChecks.block083
      · exact QuotientGeneratorBChecks.block084
      · exact QuotientGeneratorBChecks.block085
      · exact QuotientGeneratorBChecks.block086
      · exact QuotientGeneratorBChecks.block087
      · exact QuotientGeneratorBChecks.block088
      · exact QuotientGeneratorBChecks.block089
      · exact QuotientGeneratorBChecks.block090
      · exact QuotientGeneratorBChecks.block091
      · exact QuotientGeneratorBChecks.block092
      · exact QuotientGeneratorBChecks.block093
      · exact QuotientGeneratorBChecks.block094
      · exact QuotientGeneratorBChecks.block095
      · exact QuotientGeneratorBChecks.block096
      · exact QuotientGeneratorBChecks.block097
      · exact QuotientGeneratorBChecks.block098
      · exact QuotientGeneratorBChecks.block099
      · exact QuotientGeneratorBChecks.block100
      · exact QuotientGeneratorBChecks.block101
      · exact QuotientGeneratorBChecks.block102
      · exact QuotientGeneratorBChecks.block103
      · exact QuotientGeneratorBChecks.block104
      · exact QuotientGeneratorBChecks.block105
      · exact QuotientGeneratorBChecks.block106
      · exact QuotientGeneratorBChecks.block107
      · exact QuotientGeneratorBChecks.block108
      · exact QuotientGeneratorBChecks.block109
      · exact QuotientGeneratorBChecks.block110
      · exact QuotientGeneratorBChecks.block111
      · exact QuotientGeneratorBChecks.block112
      · exact QuotientGeneratorBChecks.block113
      · exact QuotientGeneratorBChecks.block114
      · exact QuotientGeneratorBChecks.block115
      · exact QuotientGeneratorBChecks.block116
      · exact QuotientGeneratorBChecks.block117
      · exact QuotientGeneratorBChecks.block118
      · exact QuotientGeneratorBChecks.block119
      · exact QuotientGeneratorBChecks.block120
      · exact QuotientGeneratorBChecks.block121
      · exact QuotientGeneratorBChecks.block122
      · exact QuotientGeneratorBChecks.block123
      · exact QuotientGeneratorBChecks.block124
      · exact QuotientGeneratorBChecks.block125
      · exact QuotientGeneratorBChecks.block126
      · exact QuotientGeneratorBChecks.block127
      · exact QuotientGeneratorBChecks.block128
      · exact QuotientGeneratorBChecks.block129
      · exact QuotientGeneratorBChecks.block130
      · exact QuotientGeneratorBChecks.block131
      · exact QuotientGeneratorBChecks.block132
      · exact QuotientGeneratorBChecks.block133
      · exact QuotientGeneratorBChecks.block134
      · exact QuotientGeneratorBChecks.block135
      · exact QuotientGeneratorBChecks.block136
      · exact QuotientGeneratorBChecks.block137
      · exact QuotientGeneratorBChecks.block138
      · exact QuotientGeneratorBChecks.block139
      · exact QuotientGeneratorBChecks.block140
      · exact QuotientGeneratorBChecks.block141
      · exact QuotientGeneratorBChecks.block142
      · exact QuotientGeneratorBChecks.block143
      · exact QuotientGeneratorBChecks.block144
      · exact QuotientGeneratorBChecks.block145
      · exact QuotientGeneratorBChecks.block146
      · exact QuotientGeneratorBChecks.block147
      · exact QuotientGeneratorBChecks.block148
      · exact QuotientGeneratorBChecks.block149
      · exact QuotientGeneratorBChecks.block150
      · exact QuotientGeneratorBChecks.block151
      · exact QuotientGeneratorBChecks.block152
      · exact QuotientGeneratorBChecks.block153
      · exact QuotientGeneratorBChecks.block154
      · exact QuotientGeneratorBChecks.block155
      · exact QuotientGeneratorBChecks.block156
      · exact QuotientGeneratorBChecks.block157
      · exact QuotientGeneratorBChecks.block158
      · exact QuotientGeneratorBChecks.block159
      · exact QuotientGeneratorBChecks.block160
      · exact QuotientGeneratorBChecks.block161
      · exact QuotientGeneratorBChecks.block162
      · exact QuotientGeneratorBChecks.block163
      · exact QuotientGeneratorBChecks.block164
      · exact QuotientGeneratorBChecks.block165
      · exact QuotientGeneratorBChecks.block166
      · exact QuotientGeneratorBChecks.block167
      · exact QuotientGeneratorBChecks.block168
      · exact QuotientGeneratorBChecks.block169
      · exact QuotientGeneratorBChecks.block170
      · exact QuotientGeneratorBChecks.block171
      · exact QuotientGeneratorBChecks.block172
      · exact QuotientGeneratorBChecks.block173
      · exact QuotientGeneratorBChecks.block174
      · exact QuotientGeneratorBChecks.block175
      · exact QuotientGeneratorBChecks.block176
      · exact QuotientGeneratorBChecks.block177
      · exact QuotientGeneratorBChecks.block178
      · exact QuotientGeneratorBChecks.block179
      · exact QuotientGeneratorBChecks.block180
      · exact QuotientGeneratorBChecks.block181
      · exact QuotientGeneratorBChecks.block182
      · exact QuotientGeneratorBChecks.block183
      · exact QuotientGeneratorBChecks.block184
    have he := checkEqualProducts_sound _ _ _ _ h j.val
    simpa only [chunk_entry _ _ _ _ j.isLt] using he
  intro i
  exact hall ⟨i.val, by omega⟩

/-- The saved intertwiner in the literal rectangular matrix coordinates. -/
theorem quotientGeneratorB :
    matrix 1474 1474 sourceTransposeB * matrix 1474 1242 quotientTransposeRows =
      matrix 1474 1242 quotientTransposeRows * matrix 1242 1242 targetB :=
  matrix_equal_products_of_rows _ _ _ _ (by decide +kernel) (by decide +kernel) rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
