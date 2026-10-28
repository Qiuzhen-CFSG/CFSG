module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-!
# Raw table relations used to shorten six inverse walks

The fixed tables satisfy the involution, inverse and order-three identities
below. Each identity is checked on every one of the 24192 points, in blocks of
128. These checks use only the raw tables. No group geometry or correctness
of the two cached subgroup actions is assumed.

The resulting rewrite rules will certify the shorter walks before they are
used in the reverse-norm column checks. Source: Columns/source/README.md and
the unchanged action arrays in Coordinates/Data.lean.
-/

-- A 128-point block was measured at 3003120 KB peak RSS. Keep the 189
-- independent kernel computations sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsTwentyToTwentySix

private def pointIndex (q : Fin 189) (r : Fin 128) : Point :=
  ⟨128 * q.val + r.val, by have := q.isLt; have := r.isLt; omega⟩

private def RelationsAt (x : Point) : Prop :=
  fastStep 0 (fastStep 0 x) = x ∧
  fastStep 1 (fastStep 3 x) = x ∧
  fastStep 3 (fastStep 1 x) = x ∧
  fastStep 1 (fastStep 1 (fastStep 1 x)) = x

private def RelationBlock (q : Fin 189) : Prop :=
  ∀ r : Fin 128, RelationsAt (pointIndex q r)

private theorem block0 : RelationBlock 0 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block1 : RelationBlock 1 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block2 : RelationBlock 2 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block3 : RelationBlock 3 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block4 : RelationBlock 4 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block5 : RelationBlock 5 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block6 : RelationBlock 6 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block7 : RelationBlock 7 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block8 : RelationBlock 8 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block9 : RelationBlock 9 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block10 : RelationBlock 10 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block11 : RelationBlock 11 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block12 : RelationBlock 12 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block13 : RelationBlock 13 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block14 : RelationBlock 14 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block15 : RelationBlock 15 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block16 : RelationBlock 16 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block17 : RelationBlock 17 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block18 : RelationBlock 18 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block19 : RelationBlock 19 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block20 : RelationBlock 20 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block21 : RelationBlock 21 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block22 : RelationBlock 22 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block23 : RelationBlock 23 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block24 : RelationBlock 24 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block25 : RelationBlock 25 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block26 : RelationBlock 26 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block27 : RelationBlock 27 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block28 : RelationBlock 28 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block29 : RelationBlock 29 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block30 : RelationBlock 30 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block31 : RelationBlock 31 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block32 : RelationBlock 32 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block33 : RelationBlock 33 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block34 : RelationBlock 34 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block35 : RelationBlock 35 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block36 : RelationBlock 36 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block37 : RelationBlock 37 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block38 : RelationBlock 38 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block39 : RelationBlock 39 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block40 : RelationBlock 40 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block41 : RelationBlock 41 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block42 : RelationBlock 42 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block43 : RelationBlock 43 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block44 : RelationBlock 44 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block45 : RelationBlock 45 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block46 : RelationBlock 46 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block47 : RelationBlock 47 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block48 : RelationBlock 48 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block49 : RelationBlock 49 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block50 : RelationBlock 50 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block51 : RelationBlock 51 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block52 : RelationBlock 52 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block53 : RelationBlock 53 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block54 : RelationBlock 54 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block55 : RelationBlock 55 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block56 : RelationBlock 56 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block57 : RelationBlock 57 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block58 : RelationBlock 58 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block59 : RelationBlock 59 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block60 : RelationBlock 60 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block61 : RelationBlock 61 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block62 : RelationBlock 62 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block63 : RelationBlock 63 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block64 : RelationBlock 64 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block65 : RelationBlock 65 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block66 : RelationBlock 66 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block67 : RelationBlock 67 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block68 : RelationBlock 68 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block69 : RelationBlock 69 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block70 : RelationBlock 70 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block71 : RelationBlock 71 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block72 : RelationBlock 72 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block73 : RelationBlock 73 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block74 : RelationBlock 74 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block75 : RelationBlock 75 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block76 : RelationBlock 76 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block77 : RelationBlock 77 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block78 : RelationBlock 78 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block79 : RelationBlock 79 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block80 : RelationBlock 80 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block81 : RelationBlock 81 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block82 : RelationBlock 82 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block83 : RelationBlock 83 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block84 : RelationBlock 84 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block85 : RelationBlock 85 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block86 : RelationBlock 86 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block87 : RelationBlock 87 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block88 : RelationBlock 88 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block89 : RelationBlock 89 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block90 : RelationBlock 90 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block91 : RelationBlock 91 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block92 : RelationBlock 92 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block93 : RelationBlock 93 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block94 : RelationBlock 94 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block95 : RelationBlock 95 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block96 : RelationBlock 96 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block97 : RelationBlock 97 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block98 : RelationBlock 98 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block99 : RelationBlock 99 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block100 : RelationBlock 100 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block101 : RelationBlock 101 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block102 : RelationBlock 102 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block103 : RelationBlock 103 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block104 : RelationBlock 104 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block105 : RelationBlock 105 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block106 : RelationBlock 106 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block107 : RelationBlock 107 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block108 : RelationBlock 108 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block109 : RelationBlock 109 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block110 : RelationBlock 110 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block111 : RelationBlock 111 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block112 : RelationBlock 112 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block113 : RelationBlock 113 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block114 : RelationBlock 114 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block115 : RelationBlock 115 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block116 : RelationBlock 116 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block117 : RelationBlock 117 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block118 : RelationBlock 118 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block119 : RelationBlock 119 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block120 : RelationBlock 120 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block121 : RelationBlock 121 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block122 : RelationBlock 122 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block123 : RelationBlock 123 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block124 : RelationBlock 124 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block125 : RelationBlock 125 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block126 : RelationBlock 126 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block127 : RelationBlock 127 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block128 : RelationBlock 128 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block129 : RelationBlock 129 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block130 : RelationBlock 130 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block131 : RelationBlock 131 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block132 : RelationBlock 132 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block133 : RelationBlock 133 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block134 : RelationBlock 134 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block135 : RelationBlock 135 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block136 : RelationBlock 136 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block137 : RelationBlock 137 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block138 : RelationBlock 138 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block139 : RelationBlock 139 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block140 : RelationBlock 140 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block141 : RelationBlock 141 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block142 : RelationBlock 142 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block143 : RelationBlock 143 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block144 : RelationBlock 144 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block145 : RelationBlock 145 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block146 : RelationBlock 146 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block147 : RelationBlock 147 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block148 : RelationBlock 148 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block149 : RelationBlock 149 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block150 : RelationBlock 150 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block151 : RelationBlock 151 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block152 : RelationBlock 152 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block153 : RelationBlock 153 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block154 : RelationBlock 154 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block155 : RelationBlock 155 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block156 : RelationBlock 156 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block157 : RelationBlock 157 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block158 : RelationBlock 158 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block159 : RelationBlock 159 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block160 : RelationBlock 160 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block161 : RelationBlock 161 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block162 : RelationBlock 162 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block163 : RelationBlock 163 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block164 : RelationBlock 164 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block165 : RelationBlock 165 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block166 : RelationBlock 166 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block167 : RelationBlock 167 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block168 : RelationBlock 168 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block169 : RelationBlock 169 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block170 : RelationBlock 170 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block171 : RelationBlock 171 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block172 : RelationBlock 172 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block173 : RelationBlock 173 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block174 : RelationBlock 174 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block175 : RelationBlock 175 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block176 : RelationBlock 176 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block177 : RelationBlock 177 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block178 : RelationBlock 178 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block179 : RelationBlock 179 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block180 : RelationBlock 180 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block181 : RelationBlock 181 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block182 : RelationBlock 182 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block183 : RelationBlock 183 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block184 : RelationBlock 184 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block185 : RelationBlock 185 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block186 : RelationBlock 186 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block187 : RelationBlock 187 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem block188 : RelationBlock 188 := by
  unfold RelationBlock RelationsAt
  decide +kernel

private theorem allBlocks (q : Fin 189) : RelationBlock q := by
  fin_cases q
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62
  · exact block63
  · exact block64
  · exact block65
  · exact block66
  · exact block67
  · exact block68
  · exact block69
  · exact block70
  · exact block71
  · exact block72
  · exact block73
  · exact block74
  · exact block75
  · exact block76
  · exact block77
  · exact block78
  · exact block79
  · exact block80
  · exact block81
  · exact block82
  · exact block83
  · exact block84
  · exact block85
  · exact block86
  · exact block87
  · exact block88
  · exact block89
  · exact block90
  · exact block91
  · exact block92
  · exact block93
  · exact block94
  · exact block95
  · exact block96
  · exact block97
  · exact block98
  · exact block99
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block104
  · exact block105
  · exact block106
  · exact block107
  · exact block108
  · exact block109
  · exact block110
  · exact block111
  · exact block112
  · exact block113
  · exact block114
  · exact block115
  · exact block116
  · exact block117
  · exact block118
  · exact block119
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block124
  · exact block125
  · exact block126
  · exact block127
  · exact block128
  · exact block129
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block134
  · exact block135
  · exact block136
  · exact block137
  · exact block138
  · exact block139
  · exact block140
  · exact block141
  · exact block142
  · exact block143
  · exact block144
  · exact block145
  · exact block146
  · exact block147
  · exact block148
  · exact block149
  · exact block150
  · exact block151
  · exact block152
  · exact block153
  · exact block154
  · exact block155
  · exact block156
  · exact block157
  · exact block158
  · exact block159
  · exact block160
  · exact block161
  · exact block162
  · exact block163
  · exact block164
  · exact block165
  · exact block166
  · exact block167
  · exact block168
  · exact block169
  · exact block170
  · exact block171
  · exact block172
  · exact block173
  · exact block174
  · exact block175
  · exact block176
  · exact block177
  · exact block178
  · exact block179
  · exact block180
  · exact block181
  · exact block182
  · exact block183
  · exact block184
  · exact block185
  · exact block186
  · exact block187
  · exact block188

private theorem relations (x : Point) : RelationsAt x := by
  let q : Fin 189 := ⟨x.val / 128, by have := x.isLt; omega⟩
  let r : Fin 128 := ⟨x.val % 128, Nat.mod_lt _ (by decide)⟩
  have h : pointIndex q r = x := by
    apply Fin.ext
    simp only [pointIndex, q, r]
    omega
  simpa only [h] using allBlocks q r

theorem step_two (x : Point) : fastStep 2 x = fastStep 0 x := rfl

theorem step_zero_zero (x : Point) : fastStep 0 (fastStep 0 x) = x :=
  (relations x).1

theorem step_one_three (x : Point) : fastStep 1 (fastStep 3 x) = x :=
  (relations x).2.1

theorem step_three_one (x : Point) : fastStep 3 (fastStep 1 x) = x :=
  (relations x).2.2.1

theorem step_one_one (x : Point) : fastStep 1 (fastStep 1 x) = fastStep 3 x := by
  have h := congrArg (fastStep 3) (relations x).2.2.2
  simpa only [step_three_one] using h

theorem step_three_three (x : Point) : fastStep 3 (fastStep 3 x) = fastStep 1 x := by
  rw [← step_one_one x, step_three_one]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsTwentyToTwentySix
