module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorA.Batch23

/-!
# Literal quotientGeneratorA matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

private theorem rows : ∀ i : Fin 1474,
    combine quotientTransposeRows sourceTransposeA[i.val]! = combine targetA quotientTransposeRows[i.val]! := by
  have hall : ∀ i : Fin (185*8),
      combine quotientTransposeRows sourceTransposeA[i.val]! = combine targetA quotientTransposeRows[i.val]! := by
    apply forall_batches (blocks := 185) (size := 8) (by decide)
      (fun i => combine quotientTransposeRows sourceTransposeA[i]! = combine targetA quotientTransposeRows[i]!)
    intro b j
    have h : checkEqualProducts quotientTransposeRows targetA
        ((sourceTransposeA.drop (b.val*8)).take 8) ((quotientTransposeRows.drop (b.val*8)).take 8) = true := by
      fin_cases b
      · exact QuotientGeneratorAChecks.block000
      · exact QuotientGeneratorAChecks.block001
      · exact QuotientGeneratorAChecks.block002
      · exact QuotientGeneratorAChecks.block003
      · exact QuotientGeneratorAChecks.block004
      · exact QuotientGeneratorAChecks.block005
      · exact QuotientGeneratorAChecks.block006
      · exact QuotientGeneratorAChecks.block007
      · exact QuotientGeneratorAChecks.block008
      · exact QuotientGeneratorAChecks.block009
      · exact QuotientGeneratorAChecks.block010
      · exact QuotientGeneratorAChecks.block011
      · exact QuotientGeneratorAChecks.block012
      · exact QuotientGeneratorAChecks.block013
      · exact QuotientGeneratorAChecks.block014
      · exact QuotientGeneratorAChecks.block015
      · exact QuotientGeneratorAChecks.block016
      · exact QuotientGeneratorAChecks.block017
      · exact QuotientGeneratorAChecks.block018
      · exact QuotientGeneratorAChecks.block019
      · exact QuotientGeneratorAChecks.block020
      · exact QuotientGeneratorAChecks.block021
      · exact QuotientGeneratorAChecks.block022
      · exact QuotientGeneratorAChecks.block023
      · exact QuotientGeneratorAChecks.block024
      · exact QuotientGeneratorAChecks.block025
      · exact QuotientGeneratorAChecks.block026
      · exact QuotientGeneratorAChecks.block027
      · exact QuotientGeneratorAChecks.block028
      · exact QuotientGeneratorAChecks.block029
      · exact QuotientGeneratorAChecks.block030
      · exact QuotientGeneratorAChecks.block031
      · exact QuotientGeneratorAChecks.block032
      · exact QuotientGeneratorAChecks.block033
      · exact QuotientGeneratorAChecks.block034
      · exact QuotientGeneratorAChecks.block035
      · exact QuotientGeneratorAChecks.block036
      · exact QuotientGeneratorAChecks.block037
      · exact QuotientGeneratorAChecks.block038
      · exact QuotientGeneratorAChecks.block039
      · exact QuotientGeneratorAChecks.block040
      · exact QuotientGeneratorAChecks.block041
      · exact QuotientGeneratorAChecks.block042
      · exact QuotientGeneratorAChecks.block043
      · exact QuotientGeneratorAChecks.block044
      · exact QuotientGeneratorAChecks.block045
      · exact QuotientGeneratorAChecks.block046
      · exact QuotientGeneratorAChecks.block047
      · exact QuotientGeneratorAChecks.block048
      · exact QuotientGeneratorAChecks.block049
      · exact QuotientGeneratorAChecks.block050
      · exact QuotientGeneratorAChecks.block051
      · exact QuotientGeneratorAChecks.block052
      · exact QuotientGeneratorAChecks.block053
      · exact QuotientGeneratorAChecks.block054
      · exact QuotientGeneratorAChecks.block055
      · exact QuotientGeneratorAChecks.block056
      · exact QuotientGeneratorAChecks.block057
      · exact QuotientGeneratorAChecks.block058
      · exact QuotientGeneratorAChecks.block059
      · exact QuotientGeneratorAChecks.block060
      · exact QuotientGeneratorAChecks.block061
      · exact QuotientGeneratorAChecks.block062
      · exact QuotientGeneratorAChecks.block063
      · exact QuotientGeneratorAChecks.block064
      · exact QuotientGeneratorAChecks.block065
      · exact QuotientGeneratorAChecks.block066
      · exact QuotientGeneratorAChecks.block067
      · exact QuotientGeneratorAChecks.block068
      · exact QuotientGeneratorAChecks.block069
      · exact QuotientGeneratorAChecks.block070
      · exact QuotientGeneratorAChecks.block071
      · exact QuotientGeneratorAChecks.block072
      · exact QuotientGeneratorAChecks.block073
      · exact QuotientGeneratorAChecks.block074
      · exact QuotientGeneratorAChecks.block075
      · exact QuotientGeneratorAChecks.block076
      · exact QuotientGeneratorAChecks.block077
      · exact QuotientGeneratorAChecks.block078
      · exact QuotientGeneratorAChecks.block079
      · exact QuotientGeneratorAChecks.block080
      · exact QuotientGeneratorAChecks.block081
      · exact QuotientGeneratorAChecks.block082
      · exact QuotientGeneratorAChecks.block083
      · exact QuotientGeneratorAChecks.block084
      · exact QuotientGeneratorAChecks.block085
      · exact QuotientGeneratorAChecks.block086
      · exact QuotientGeneratorAChecks.block087
      · exact QuotientGeneratorAChecks.block088
      · exact QuotientGeneratorAChecks.block089
      · exact QuotientGeneratorAChecks.block090
      · exact QuotientGeneratorAChecks.block091
      · exact QuotientGeneratorAChecks.block092
      · exact QuotientGeneratorAChecks.block093
      · exact QuotientGeneratorAChecks.block094
      · exact QuotientGeneratorAChecks.block095
      · exact QuotientGeneratorAChecks.block096
      · exact QuotientGeneratorAChecks.block097
      · exact QuotientGeneratorAChecks.block098
      · exact QuotientGeneratorAChecks.block099
      · exact QuotientGeneratorAChecks.block100
      · exact QuotientGeneratorAChecks.block101
      · exact QuotientGeneratorAChecks.block102
      · exact QuotientGeneratorAChecks.block103
      · exact QuotientGeneratorAChecks.block104
      · exact QuotientGeneratorAChecks.block105
      · exact QuotientGeneratorAChecks.block106
      · exact QuotientGeneratorAChecks.block107
      · exact QuotientGeneratorAChecks.block108
      · exact QuotientGeneratorAChecks.block109
      · exact QuotientGeneratorAChecks.block110
      · exact QuotientGeneratorAChecks.block111
      · exact QuotientGeneratorAChecks.block112
      · exact QuotientGeneratorAChecks.block113
      · exact QuotientGeneratorAChecks.block114
      · exact QuotientGeneratorAChecks.block115
      · exact QuotientGeneratorAChecks.block116
      · exact QuotientGeneratorAChecks.block117
      · exact QuotientGeneratorAChecks.block118
      · exact QuotientGeneratorAChecks.block119
      · exact QuotientGeneratorAChecks.block120
      · exact QuotientGeneratorAChecks.block121
      · exact QuotientGeneratorAChecks.block122
      · exact QuotientGeneratorAChecks.block123
      · exact QuotientGeneratorAChecks.block124
      · exact QuotientGeneratorAChecks.block125
      · exact QuotientGeneratorAChecks.block126
      · exact QuotientGeneratorAChecks.block127
      · exact QuotientGeneratorAChecks.block128
      · exact QuotientGeneratorAChecks.block129
      · exact QuotientGeneratorAChecks.block130
      · exact QuotientGeneratorAChecks.block131
      · exact QuotientGeneratorAChecks.block132
      · exact QuotientGeneratorAChecks.block133
      · exact QuotientGeneratorAChecks.block134
      · exact QuotientGeneratorAChecks.block135
      · exact QuotientGeneratorAChecks.block136
      · exact QuotientGeneratorAChecks.block137
      · exact QuotientGeneratorAChecks.block138
      · exact QuotientGeneratorAChecks.block139
      · exact QuotientGeneratorAChecks.block140
      · exact QuotientGeneratorAChecks.block141
      · exact QuotientGeneratorAChecks.block142
      · exact QuotientGeneratorAChecks.block143
      · exact QuotientGeneratorAChecks.block144
      · exact QuotientGeneratorAChecks.block145
      · exact QuotientGeneratorAChecks.block146
      · exact QuotientGeneratorAChecks.block147
      · exact QuotientGeneratorAChecks.block148
      · exact QuotientGeneratorAChecks.block149
      · exact QuotientGeneratorAChecks.block150
      · exact QuotientGeneratorAChecks.block151
      · exact QuotientGeneratorAChecks.block152
      · exact QuotientGeneratorAChecks.block153
      · exact QuotientGeneratorAChecks.block154
      · exact QuotientGeneratorAChecks.block155
      · exact QuotientGeneratorAChecks.block156
      · exact QuotientGeneratorAChecks.block157
      · exact QuotientGeneratorAChecks.block158
      · exact QuotientGeneratorAChecks.block159
      · exact QuotientGeneratorAChecks.block160
      · exact QuotientGeneratorAChecks.block161
      · exact QuotientGeneratorAChecks.block162
      · exact QuotientGeneratorAChecks.block163
      · exact QuotientGeneratorAChecks.block164
      · exact QuotientGeneratorAChecks.block165
      · exact QuotientGeneratorAChecks.block166
      · exact QuotientGeneratorAChecks.block167
      · exact QuotientGeneratorAChecks.block168
      · exact QuotientGeneratorAChecks.block169
      · exact QuotientGeneratorAChecks.block170
      · exact QuotientGeneratorAChecks.block171
      · exact QuotientGeneratorAChecks.block172
      · exact QuotientGeneratorAChecks.block173
      · exact QuotientGeneratorAChecks.block174
      · exact QuotientGeneratorAChecks.block175
      · exact QuotientGeneratorAChecks.block176
      · exact QuotientGeneratorAChecks.block177
      · exact QuotientGeneratorAChecks.block178
      · exact QuotientGeneratorAChecks.block179
      · exact QuotientGeneratorAChecks.block180
      · exact QuotientGeneratorAChecks.block181
      · exact QuotientGeneratorAChecks.block182
      · exact QuotientGeneratorAChecks.block183
      · exact QuotientGeneratorAChecks.block184
    have he := checkEqualProducts_sound _ _ _ _ h j.val
    simpa only [chunk_entry _ _ _ _ j.isLt] using he
  intro i
  exact hall ⟨i.val, by omega⟩

/-- The saved intertwiner in the literal rectangular matrix coordinates. -/
theorem quotientGeneratorA :
    matrix 1474 1474 sourceTransposeA * matrix 1474 1242 quotientTransposeRows =
      matrix 1474 1242 quotientTransposeRows * matrix 1242 1242 targetA :=
  matrix_equal_products_of_rows _ _ _ _ (by decide +kernel) (by decide +kernel) rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
