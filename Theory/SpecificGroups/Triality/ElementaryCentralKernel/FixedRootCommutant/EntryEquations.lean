module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Equations

/-! Explicit entry equations used by the elimination certificates.
Each is a specialization of `constant_equation`, hence a genuine matrix
commutator equation. The numbering is `784 * generator + 28 * row + column`.
-/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
variable {F : Type*} [CommRing F] [CharP F 2]
variable (A : Matrix (Fin 28) (Fin 28) F) (h : ∀ k, Commute A (constantMatrix k))
include h

lemma equation_0 : (A 0 0 + A 0 17) + (A 0 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 0

lemma equation_5 : (A 0 5 + A 0 9) + (A 0 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 5

lemma equation_7 : (A 0 7 + A 0 11) + (A 0 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 7

lemma equation_8 : (A 0 4 + A 0 8) + (A 0 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 8

lemma equation_10 : (A 0 6 + A 0 10) + (A 0 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 10

lemma equation_18 : (A 0 1 + A 0 17 + A 0 18) + (A 0 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 18

lemma equation_22 : (A 0 22 + A 0 26) + (A 0 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 22

lemma equation_23 : (A 0 23 + A 0 27) + (A 0 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 23

lemma equation_24 : (A 0 20 + A 0 24) + (A 0 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 24

lemma equation_25 : (A 0 21 + A 0 25) + (A 0 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 0 25

lemma equation_28 : (A 1 0 + A 1 17) + (A 1 0 + A 18 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 0

lemma equation_29 : (A 1 1) + (A 1 1 + A 18 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 1

lemma equation_30 : (A 1 2 + A 1 17) + (A 1 2 + A 18 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 2

lemma equation_31 : (A 1 3 + A 1 17) + (A 1 3 + A 18 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 3

lemma equation_32 : (A 1 4) + (A 1 4 + A 18 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 4

lemma equation_33 : (A 1 5 + A 1 9) + (A 1 5 + A 18 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 5

lemma equation_34 : (A 1 6) + (A 1 6 + A 18 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 6

lemma equation_35 : (A 1 7 + A 1 11) + (A 1 7 + A 18 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 7

lemma equation_36 : (A 1 4 + A 1 8) + (A 1 8 + A 18 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 8

lemma equation_37 : (A 1 9) + (A 1 9 + A 18 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 9

lemma equation_38 : (A 1 6 + A 1 10) + (A 1 10 + A 18 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 10

lemma equation_39 : (A 1 11) + (A 1 11 + A 18 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 11

lemma equation_40 : (A 1 12) + (A 1 12 + A 18 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 12

lemma equation_41 : (A 1 13) + (A 1 13 + A 18 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 13

lemma equation_42 : (A 1 14) + (A 1 14 + A 18 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 14

lemma equation_43 : (A 1 15) + (A 1 15 + A 18 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 15

lemma equation_44 : (A 1 16) + (A 1 16 + A 18 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 16

lemma equation_45 : (A 1 17) + (A 1 17 + A 18 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 17

lemma equation_46 : (A 1 1 + A 1 17 + A 1 18) + (A 1 18 + A 18 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 18

lemma equation_47 : (A 1 19) + (A 1 19 + A 18 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 19

lemma equation_48 : (A 1 20) + (A 1 20 + A 18 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 20

lemma equation_49 : (A 1 21) + (A 1 21 + A 18 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 21

lemma equation_50 : (A 1 22 + A 1 26) + (A 1 22 + A 18 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 22

lemma equation_51 : (A 1 23 + A 1 27) + (A 1 23 + A 18 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 23

lemma equation_52 : (A 1 20 + A 1 24) + (A 1 24 + A 18 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 24

lemma equation_53 : (A 1 21 + A 1 25) + (A 1 25 + A 18 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 25

lemma equation_54 : (A 1 26) + (A 1 26 + A 18 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 26

lemma equation_55 : (A 1 27) + (A 1 27 + A 18 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 1 27

lemma equation_56 : (A 2 0 + A 2 17) + (A 2 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 0

lemma equation_61 : (A 2 5 + A 2 9) + (A 2 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 5

lemma equation_63 : (A 2 7 + A 2 11) + (A 2 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 7

lemma equation_64 : (A 2 4 + A 2 8) + (A 2 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 8

lemma equation_66 : (A 2 6 + A 2 10) + (A 2 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 10

lemma equation_74 : (A 2 1 + A 2 17 + A 2 18) + (A 2 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 18

lemma equation_78 : (A 2 22 + A 2 26) + (A 2 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 22

lemma equation_79 : (A 2 23 + A 2 27) + (A 2 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 23

lemma equation_80 : (A 2 20 + A 2 24) + (A 2 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 24

lemma equation_81 : (A 2 21 + A 2 25) + (A 2 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 2 25

lemma equation_84 : (A 3 0 + A 3 17) + (A 3 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 0

lemma equation_89 : (A 3 5 + A 3 9) + (A 3 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 5

lemma equation_91 : (A 3 7 + A 3 11) + (A 3 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 7

lemma equation_92 : (A 3 4 + A 3 8) + (A 3 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 8

lemma equation_94 : (A 3 6 + A 3 10) + (A 3 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 10

lemma equation_102 : (A 3 1 + A 3 17 + A 3 18) + (A 3 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 18

lemma equation_106 : (A 3 22 + A 3 26) + (A 3 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 22

lemma equation_107 : (A 3 23 + A 3 27) + (A 3 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 23

lemma equation_108 : (A 3 20 + A 3 24) + (A 3 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 24

lemma equation_109 : (A 3 21 + A 3 25) + (A 3 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 3 25

lemma equation_112 : (A 4 0 + A 4 17) + (A 4 0 + A 8 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 0

lemma equation_113 : (A 4 1) + (A 4 1 + A 8 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 1

lemma equation_114 : (A 4 2 + A 4 17) + (A 4 2 + A 8 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 2

lemma equation_115 : (A 4 3 + A 4 17) + (A 4 3 + A 8 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 3

lemma equation_116 : (A 4 4) + (A 4 4 + A 8 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 4

lemma equation_117 : (A 4 5 + A 4 9) + (A 4 5 + A 8 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 5

lemma equation_118 : (A 4 6) + (A 4 6 + A 8 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 6

lemma equation_119 : (A 4 7 + A 4 11) + (A 4 7 + A 8 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 7

lemma equation_120 : (A 4 4 + A 4 8) + (A 4 8 + A 8 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 8

lemma equation_121 : (A 4 9) + (A 4 9 + A 8 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 9

lemma equation_122 : (A 4 6 + A 4 10) + (A 4 10 + A 8 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 10

lemma equation_123 : (A 4 11) + (A 4 11 + A 8 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 11

lemma equation_124 : (A 4 12) + (A 4 12 + A 8 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 12

lemma equation_125 : (A 4 13) + (A 4 13 + A 8 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 13

lemma equation_126 : (A 4 14) + (A 4 14 + A 8 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 14

lemma equation_127 : (A 4 15) + (A 4 15 + A 8 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 15

lemma equation_128 : (A 4 16) + (A 4 16 + A 8 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 16

lemma equation_129 : (A 4 17) + (A 4 17 + A 8 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 17

lemma equation_130 : (A 4 1 + A 4 17 + A 4 18) + (A 4 18 + A 8 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 18

lemma equation_131 : (A 4 19) + (A 4 19 + A 8 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 19

lemma equation_132 : (A 4 20) + (A 4 20 + A 8 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 20

lemma equation_133 : (A 4 21) + (A 4 21 + A 8 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 21

lemma equation_134 : (A 4 22 + A 4 26) + (A 4 22 + A 8 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 22

lemma equation_135 : (A 4 23 + A 4 27) + (A 4 23 + A 8 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 23

lemma equation_136 : (A 4 20 + A 4 24) + (A 4 24 + A 8 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 24

lemma equation_137 : (A 4 21 + A 4 25) + (A 4 25 + A 8 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 25

lemma equation_138 : (A 4 26) + (A 4 26 + A 8 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 26

lemma equation_139 : (A 4 27) + (A 4 27 + A 8 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 4 27

lemma equation_140 : (A 5 0 + A 5 17) + (A 5 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 0

lemma equation_145 : (A 5 5 + A 5 9) + (A 5 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 5

lemma equation_147 : (A 5 7 + A 5 11) + (A 5 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 7

lemma equation_148 : (A 5 4 + A 5 8) + (A 5 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 8

lemma equation_150 : (A 5 6 + A 5 10) + (A 5 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 10

lemma equation_158 : (A 5 1 + A 5 17 + A 5 18) + (A 5 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 18

lemma equation_162 : (A 5 22 + A 5 26) + (A 5 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 22

lemma equation_163 : (A 5 23 + A 5 27) + (A 5 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 23

lemma equation_164 : (A 5 20 + A 5 24) + (A 5 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 24

lemma equation_165 : (A 5 21 + A 5 25) + (A 5 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 5 25

lemma equation_168 : (A 6 0 + A 6 17) + (A 6 0 + A 10 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 0

lemma equation_169 : (A 6 1) + (A 6 1 + A 10 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 1

lemma equation_170 : (A 6 2 + A 6 17) + (A 6 2 + A 10 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 2

lemma equation_171 : (A 6 3 + A 6 17) + (A 6 3 + A 10 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 3

lemma equation_172 : (A 6 4) + (A 6 4 + A 10 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 4

lemma equation_173 : (A 6 5 + A 6 9) + (A 6 5 + A 10 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 5

lemma equation_174 : (A 6 6) + (A 6 6 + A 10 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 6

lemma equation_175 : (A 6 7 + A 6 11) + (A 6 7 + A 10 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 7

lemma equation_176 : (A 6 4 + A 6 8) + (A 6 8 + A 10 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 8

lemma equation_177 : (A 6 9) + (A 6 9 + A 10 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 9

lemma equation_178 : (A 6 6 + A 6 10) + (A 6 10 + A 10 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 10

lemma equation_179 : (A 6 11) + (A 6 11 + A 10 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 11

lemma equation_180 : (A 6 12) + (A 6 12 + A 10 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 12

lemma equation_181 : (A 6 13) + (A 6 13 + A 10 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 13

lemma equation_182 : (A 6 14) + (A 6 14 + A 10 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 14

lemma equation_183 : (A 6 15) + (A 6 15 + A 10 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 15

lemma equation_184 : (A 6 16) + (A 6 16 + A 10 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 16

lemma equation_185 : (A 6 17) + (A 6 17 + A 10 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 17

lemma equation_186 : (A 6 1 + A 6 17 + A 6 18) + (A 6 18 + A 10 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 18

lemma equation_187 : (A 6 19) + (A 6 19 + A 10 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 19

lemma equation_188 : (A 6 20) + (A 6 20 + A 10 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 20

lemma equation_189 : (A 6 21) + (A 6 21 + A 10 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 21

lemma equation_190 : (A 6 22 + A 6 26) + (A 6 22 + A 10 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 22

lemma equation_191 : (A 6 23 + A 6 27) + (A 6 23 + A 10 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 23

lemma equation_192 : (A 6 20 + A 6 24) + (A 6 24 + A 10 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 24

lemma equation_193 : (A 6 21 + A 6 25) + (A 6 25 + A 10 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 25

lemma equation_194 : (A 6 26) + (A 6 26 + A 10 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 26

lemma equation_195 : (A 6 27) + (A 6 27 + A 10 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 6 27

lemma equation_196 : (A 7 0 + A 7 17) + (A 7 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 0

lemma equation_201 : (A 7 5 + A 7 9) + (A 7 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 5

lemma equation_203 : (A 7 7 + A 7 11) + (A 7 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 7

lemma equation_204 : (A 7 4 + A 7 8) + (A 7 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 8

lemma equation_206 : (A 7 6 + A 7 10) + (A 7 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 10

lemma equation_214 : (A 7 1 + A 7 17 + A 7 18) + (A 7 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 18

lemma equation_218 : (A 7 22 + A 7 26) + (A 7 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 22

lemma equation_219 : (A 7 23 + A 7 27) + (A 7 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 23

lemma equation_220 : (A 7 20 + A 7 24) + (A 7 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 24

lemma equation_221 : (A 7 21 + A 7 25) + (A 7 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 7 25

lemma equation_252 : (A 9 0 + A 9 17) + (A 5 0 + A 9 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 0

lemma equation_254 : (A 9 2 + A 9 17) + (A 5 2 + A 9 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 2

lemma equation_255 : (A 9 3 + A 9 17) + (A 5 3 + A 9 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 3

lemma equation_257 : (A 9 5 + A 9 9) + (A 5 5 + A 9 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 5

lemma equation_259 : (A 9 7 + A 9 11) + (A 5 7 + A 9 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 7

lemma equation_260 : (A 9 4 + A 9 8) + (A 5 8 + A 9 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 8

lemma equation_262 : (A 9 6 + A 9 10) + (A 5 10 + A 9 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 10

lemma equation_264 : (A 9 12) + (A 5 12 + A 9 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 12

lemma equation_265 : (A 9 13) + (A 5 13 + A 9 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 13

lemma equation_266 : (A 9 14) + (A 5 14 + A 9 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 14

lemma equation_267 : (A 9 15) + (A 5 15 + A 9 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 15

lemma equation_268 : (A 9 16) + (A 5 16 + A 9 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 16

lemma equation_270 : (A 9 1 + A 9 17 + A 9 18) + (A 5 18 + A 9 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 18

lemma equation_271 : (A 9 19) + (A 5 19 + A 9 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 19

lemma equation_274 : (A 9 22 + A 9 26) + (A 5 22 + A 9 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 22

lemma equation_275 : (A 9 23 + A 9 27) + (A 5 23 + A 9 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 23

lemma equation_276 : (A 9 20 + A 9 24) + (A 5 24 + A 9 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 24

lemma equation_277 : (A 9 21 + A 9 25) + (A 5 25 + A 9 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 9 25

lemma equation_308 : (A 11 0 + A 11 17) + (A 7 0 + A 11 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 0

lemma equation_310 : (A 11 2 + A 11 17) + (A 7 2 + A 11 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 2

lemma equation_311 : (A 11 3 + A 11 17) + (A 7 3 + A 11 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 3

lemma equation_313 : (A 11 5 + A 11 9) + (A 7 5 + A 11 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 5

lemma equation_315 : (A 11 7 + A 11 11) + (A 7 7 + A 11 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 7

lemma equation_316 : (A 11 4 + A 11 8) + (A 7 8 + A 11 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 8

lemma equation_318 : (A 11 6 + A 11 10) + (A 7 10 + A 11 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 10

lemma equation_320 : (A 11 12) + (A 7 12 + A 11 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 12

lemma equation_321 : (A 11 13) + (A 7 13 + A 11 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 13

lemma equation_322 : (A 11 14) + (A 7 14 + A 11 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 14

lemma equation_323 : (A 11 15) + (A 7 15 + A 11 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 15

lemma equation_324 : (A 11 16) + (A 7 16 + A 11 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 16

lemma equation_326 : (A 11 1 + A 11 17 + A 11 18) + (A 7 18 + A 11 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 18

lemma equation_327 : (A 11 19) + (A 7 19 + A 11 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 19

lemma equation_330 : (A 11 22 + A 11 26) + (A 7 22 + A 11 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 22

lemma equation_331 : (A 11 23 + A 11 27) + (A 7 23 + A 11 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 23

lemma equation_332 : (A 11 20 + A 11 24) + (A 7 24 + A 11 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 24

lemma equation_333 : (A 11 21 + A 11 25) + (A 7 25 + A 11 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 11 25

lemma equation_336 : (A 12 0 + A 12 17) + (A 12 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 0

lemma equation_341 : (A 12 5 + A 12 9) + (A 12 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 5

lemma equation_343 : (A 12 7 + A 12 11) + (A 12 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 7

lemma equation_344 : (A 12 4 + A 12 8) + (A 12 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 8

lemma equation_346 : (A 12 6 + A 12 10) + (A 12 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 10

lemma equation_354 : (A 12 1 + A 12 17 + A 12 18) + (A 12 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 18

lemma equation_358 : (A 12 22 + A 12 26) + (A 12 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 22

lemma equation_359 : (A 12 23 + A 12 27) + (A 12 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 23

lemma equation_360 : (A 12 20 + A 12 24) + (A 12 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 24

lemma equation_361 : (A 12 21 + A 12 25) + (A 12 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 12 25

lemma equation_364 : (A 13 0 + A 13 17) + (A 13 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 0

lemma equation_369 : (A 13 5 + A 13 9) + (A 13 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 5

lemma equation_371 : (A 13 7 + A 13 11) + (A 13 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 7

lemma equation_372 : (A 13 4 + A 13 8) + (A 13 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 8

lemma equation_374 : (A 13 6 + A 13 10) + (A 13 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 10

lemma equation_382 : (A 13 1 + A 13 17 + A 13 18) + (A 13 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 18

lemma equation_386 : (A 13 22 + A 13 26) + (A 13 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 22

lemma equation_387 : (A 13 23 + A 13 27) + (A 13 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 23

lemma equation_388 : (A 13 20 + A 13 24) + (A 13 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 24

lemma equation_389 : (A 13 21 + A 13 25) + (A 13 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 13 25

lemma equation_392 : (A 14 0 + A 14 17) + (A 14 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 0

lemma equation_397 : (A 14 5 + A 14 9) + (A 14 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 5

lemma equation_399 : (A 14 7 + A 14 11) + (A 14 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 7

lemma equation_400 : (A 14 4 + A 14 8) + (A 14 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 8

lemma equation_402 : (A 14 6 + A 14 10) + (A 14 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 10

lemma equation_410 : (A 14 1 + A 14 17 + A 14 18) + (A 14 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 18

lemma equation_414 : (A 14 22 + A 14 26) + (A 14 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 22

lemma equation_415 : (A 14 23 + A 14 27) + (A 14 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 23

lemma equation_416 : (A 14 20 + A 14 24) + (A 14 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 24

lemma equation_417 : (A 14 21 + A 14 25) + (A 14 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 14 25

lemma equation_420 : (A 15 0 + A 15 17) + (A 15 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 0

lemma equation_425 : (A 15 5 + A 15 9) + (A 15 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 5

lemma equation_427 : (A 15 7 + A 15 11) + (A 15 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 7

lemma equation_428 : (A 15 4 + A 15 8) + (A 15 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 8

lemma equation_430 : (A 15 6 + A 15 10) + (A 15 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 10

lemma equation_438 : (A 15 1 + A 15 17 + A 15 18) + (A 15 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 18

lemma equation_442 : (A 15 22 + A 15 26) + (A 15 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 22

lemma equation_443 : (A 15 23 + A 15 27) + (A 15 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 23

lemma equation_444 : (A 15 20 + A 15 24) + (A 15 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 24

lemma equation_445 : (A 15 21 + A 15 25) + (A 15 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 15 25

lemma equation_448 : (A 16 0 + A 16 17) + (A 16 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 0

lemma equation_453 : (A 16 5 + A 16 9) + (A 16 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 5

lemma equation_455 : (A 16 7 + A 16 11) + (A 16 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 7

lemma equation_456 : (A 16 4 + A 16 8) + (A 16 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 8

lemma equation_458 : (A 16 6 + A 16 10) + (A 16 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 10

lemma equation_466 : (A 16 1 + A 16 17 + A 16 18) + (A 16 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 18

lemma equation_470 : (A 16 22 + A 16 26) + (A 16 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 22

lemma equation_471 : (A 16 23 + A 16 27) + (A 16 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 23

lemma equation_472 : (A 16 20 + A 16 24) + (A 16 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 24

lemma equation_473 : (A 16 21 + A 16 25) + (A 16 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 16 25

lemma equation_476 : (A 17 0 + A 17 17) + (A 0 0 + A 2 0 + A 3 0 + A 17 0 + A 18 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 0

lemma equation_478 : (A 17 2 + A 17 17) + (A 0 2 + A 2 2 + A 3 2 + A 17 2 + A 18 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 2

lemma equation_479 : (A 17 3 + A 17 17) + (A 0 3 + A 2 3 + A 3 3 + A 17 3 + A 18 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 3

lemma equation_481 : (A 17 5 + A 17 9) + (A 0 5 + A 2 5 + A 3 5 + A 17 5 + A 18 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 5

lemma equation_483 : (A 17 7 + A 17 11) + (A 0 7 + A 2 7 + A 3 7 + A 17 7 + A 18 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 7

lemma equation_484 : (A 17 4 + A 17 8) + (A 0 8 + A 2 8 + A 3 8 + A 17 8 + A 18 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 8

lemma equation_486 : (A 17 6 + A 17 10) + (A 0 10 + A 2 10 + A 3 10 + A 17 10 + A 18 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 10

lemma equation_488 : (A 17 12) + (A 0 12 + A 2 12 + A 3 12 + A 17 12 + A 18 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 12

lemma equation_489 : (A 17 13) + (A 0 13 + A 2 13 + A 3 13 + A 17 13 + A 18 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 13

lemma equation_490 : (A 17 14) + (A 0 14 + A 2 14 + A 3 14 + A 17 14 + A 18 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 14

lemma equation_491 : (A 17 15) + (A 0 15 + A 2 15 + A 3 15 + A 17 15 + A 18 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 15

lemma equation_492 : (A 17 16) + (A 0 16 + A 2 16 + A 3 16 + A 17 16 + A 18 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 16

lemma equation_494 : (A 17 1 + A 17 17 + A 17 18) + (A 0 18 + A 2 18 + A 3 18 + A 17 18 + A 18 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 18

lemma equation_495 : (A 17 19) + (A 0 19 + A 2 19 + A 3 19 + A 17 19 + A 18 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 19

lemma equation_498 : (A 17 22 + A 17 26) + (A 0 22 + A 2 22 + A 3 22 + A 17 22 + A 18 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 22

lemma equation_499 : (A 17 23 + A 17 27) + (A 0 23 + A 2 23 + A 3 23 + A 17 23 + A 18 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 23

lemma equation_500 : (A 17 20 + A 17 24) + (A 0 24 + A 2 24 + A 3 24 + A 17 24 + A 18 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 24

lemma equation_501 : (A 17 21 + A 17 25) + (A 0 25 + A 2 25 + A 3 25 + A 17 25 + A 18 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 17 25

lemma equation_532 : (A 19 0 + A 19 17) + (A 19 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 0

lemma equation_537 : (A 19 5 + A 19 9) + (A 19 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 5

lemma equation_539 : (A 19 7 + A 19 11) + (A 19 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 7

lemma equation_540 : (A 19 4 + A 19 8) + (A 19 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 8

lemma equation_542 : (A 19 6 + A 19 10) + (A 19 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 10

lemma equation_550 : (A 19 1 + A 19 17 + A 19 18) + (A 19 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 18

lemma equation_554 : (A 19 22 + A 19 26) + (A 19 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 22

lemma equation_555 : (A 19 23 + A 19 27) + (A 19 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 23

lemma equation_556 : (A 19 20 + A 19 24) + (A 19 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 24

lemma equation_557 : (A 19 21 + A 19 25) + (A 19 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 19 25

lemma equation_560 : (A 20 0 + A 20 17) + (A 20 0 + A 24 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 0

lemma equation_561 : (A 20 1) + (A 20 1 + A 24 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 1

lemma equation_562 : (A 20 2 + A 20 17) + (A 20 2 + A 24 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 2

lemma equation_563 : (A 20 3 + A 20 17) + (A 20 3 + A 24 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 3

lemma equation_564 : (A 20 4) + (A 20 4 + A 24 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 4

lemma equation_565 : (A 20 5 + A 20 9) + (A 20 5 + A 24 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 5

lemma equation_566 : (A 20 6) + (A 20 6 + A 24 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 6

lemma equation_567 : (A 20 7 + A 20 11) + (A 20 7 + A 24 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 7

lemma equation_568 : (A 20 4 + A 20 8) + (A 20 8 + A 24 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 8

lemma equation_569 : (A 20 9) + (A 20 9 + A 24 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 9

lemma equation_570 : (A 20 6 + A 20 10) + (A 20 10 + A 24 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 10

lemma equation_571 : (A 20 11) + (A 20 11 + A 24 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 11

lemma equation_572 : (A 20 12) + (A 20 12 + A 24 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 12

lemma equation_573 : (A 20 13) + (A 20 13 + A 24 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 13

lemma equation_574 : (A 20 14) + (A 20 14 + A 24 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 14

lemma equation_575 : (A 20 15) + (A 20 15 + A 24 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 15

lemma equation_576 : (A 20 16) + (A 20 16 + A 24 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 16

lemma equation_577 : (A 20 17) + (A 20 17 + A 24 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 17

lemma equation_578 : (A 20 1 + A 20 17 + A 20 18) + (A 20 18 + A 24 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 18

lemma equation_579 : (A 20 19) + (A 20 19 + A 24 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 19

lemma equation_580 : (A 20 20) + (A 20 20 + A 24 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 20

lemma equation_581 : (A 20 21) + (A 20 21 + A 24 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 21

lemma equation_582 : (A 20 22 + A 20 26) + (A 20 22 + A 24 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 22

lemma equation_583 : (A 20 23 + A 20 27) + (A 20 23 + A 24 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 23

lemma equation_584 : (A 20 20 + A 20 24) + (A 20 24 + A 24 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 24

lemma equation_585 : (A 20 21 + A 20 25) + (A 20 25 + A 24 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 25

lemma equation_586 : (A 20 26) + (A 20 26 + A 24 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 26

lemma equation_587 : (A 20 27) + (A 20 27 + A 24 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 20 27

lemma equation_588 : (A 21 0 + A 21 17) + (A 21 0 + A 25 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 0

lemma equation_589 : (A 21 1) + (A 21 1 + A 25 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 1

lemma equation_590 : (A 21 2 + A 21 17) + (A 21 2 + A 25 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 2

lemma equation_591 : (A 21 3 + A 21 17) + (A 21 3 + A 25 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 3

lemma equation_592 : (A 21 4) + (A 21 4 + A 25 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 4

lemma equation_593 : (A 21 5 + A 21 9) + (A 21 5 + A 25 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 5

lemma equation_594 : (A 21 6) + (A 21 6 + A 25 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 6

lemma equation_595 : (A 21 7 + A 21 11) + (A 21 7 + A 25 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 7

lemma equation_596 : (A 21 4 + A 21 8) + (A 21 8 + A 25 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 8

lemma equation_597 : (A 21 9) + (A 21 9 + A 25 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 9

lemma equation_598 : (A 21 6 + A 21 10) + (A 21 10 + A 25 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 10

lemma equation_599 : (A 21 11) + (A 21 11 + A 25 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 11

lemma equation_600 : (A 21 12) + (A 21 12 + A 25 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 12

lemma equation_601 : (A 21 13) + (A 21 13 + A 25 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 13

lemma equation_602 : (A 21 14) + (A 21 14 + A 25 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 14

lemma equation_603 : (A 21 15) + (A 21 15 + A 25 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 15

lemma equation_604 : (A 21 16) + (A 21 16 + A 25 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 16

lemma equation_605 : (A 21 17) + (A 21 17 + A 25 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 17

lemma equation_606 : (A 21 1 + A 21 17 + A 21 18) + (A 21 18 + A 25 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 18

lemma equation_607 : (A 21 19) + (A 21 19 + A 25 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 19

lemma equation_608 : (A 21 20) + (A 21 20 + A 25 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 20

lemma equation_609 : (A 21 21) + (A 21 21 + A 25 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 21

lemma equation_610 : (A 21 22 + A 21 26) + (A 21 22 + A 25 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 22

lemma equation_611 : (A 21 23 + A 21 27) + (A 21 23 + A 25 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 23

lemma equation_612 : (A 21 20 + A 21 24) + (A 21 24 + A 25 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 24

lemma equation_613 : (A 21 21 + A 21 25) + (A 21 25 + A 25 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 25

lemma equation_614 : (A 21 26) + (A 21 26 + A 25 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 26

lemma equation_615 : (A 21 27) + (A 21 27 + A 25 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 21 27

lemma equation_616 : (A 22 0 + A 22 17) + (A 22 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 0

lemma equation_621 : (A 22 5 + A 22 9) + (A 22 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 5

lemma equation_623 : (A 22 7 + A 22 11) + (A 22 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 7

lemma equation_624 : (A 22 4 + A 22 8) + (A 22 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 8

lemma equation_626 : (A 22 6 + A 22 10) + (A 22 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 10

lemma equation_634 : (A 22 1 + A 22 17 + A 22 18) + (A 22 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 18

lemma equation_638 : (A 22 22 + A 22 26) + (A 22 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 22

lemma equation_639 : (A 22 23 + A 22 27) + (A 22 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 23

lemma equation_640 : (A 22 20 + A 22 24) + (A 22 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 24

lemma equation_641 : (A 22 21 + A 22 25) + (A 22 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 22 25

lemma equation_644 : (A 23 0 + A 23 17) + (A 23 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 0

lemma equation_649 : (A 23 5 + A 23 9) + (A 23 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 5

lemma equation_651 : (A 23 7 + A 23 11) + (A 23 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 7

lemma equation_652 : (A 23 4 + A 23 8) + (A 23 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 8

lemma equation_654 : (A 23 6 + A 23 10) + (A 23 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 10

lemma equation_662 : (A 23 1 + A 23 17 + A 23 18) + (A 23 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 18

lemma equation_666 : (A 23 22 + A 23 26) + (A 23 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 22

lemma equation_667 : (A 23 23 + A 23 27) + (A 23 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 23

lemma equation_668 : (A 23 20 + A 23 24) + (A 23 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 24

lemma equation_669 : (A 23 21 + A 23 25) + (A 23 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 23 25

lemma equation_728 : (A 26 0 + A 26 17) + (A 22 0 + A 26 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 0

lemma equation_730 : (A 26 2 + A 26 17) + (A 22 2 + A 26 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 2

lemma equation_731 : (A 26 3 + A 26 17) + (A 22 3 + A 26 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 3

lemma equation_733 : (A 26 5 + A 26 9) + (A 22 5 + A 26 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 5

lemma equation_735 : (A 26 7 + A 26 11) + (A 22 7 + A 26 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 7

lemma equation_736 : (A 26 4 + A 26 8) + (A 22 8 + A 26 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 8

lemma equation_738 : (A 26 6 + A 26 10) + (A 22 10 + A 26 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 10

lemma equation_740 : (A 26 12) + (A 22 12 + A 26 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 12

lemma equation_741 : (A 26 13) + (A 22 13 + A 26 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 13

lemma equation_742 : (A 26 14) + (A 22 14 + A 26 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 14

lemma equation_743 : (A 26 15) + (A 22 15 + A 26 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 15

lemma equation_744 : (A 26 16) + (A 22 16 + A 26 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 16

lemma equation_746 : (A 26 1 + A 26 17 + A 26 18) + (A 22 18 + A 26 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 18

lemma equation_747 : (A 26 19) + (A 22 19 + A 26 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 19

lemma equation_750 : (A 26 22 + A 26 26) + (A 22 22 + A 26 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 22

lemma equation_751 : (A 26 23 + A 26 27) + (A 22 23 + A 26 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 23

lemma equation_752 : (A 26 20 + A 26 24) + (A 22 24 + A 26 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 24

lemma equation_753 : (A 26 21 + A 26 25) + (A 22 25 + A 26 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 26 25

lemma equation_756 : (A 27 0 + A 27 17) + (A 23 0 + A 27 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 0

lemma equation_758 : (A 27 2 + A 27 17) + (A 23 2 + A 27 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 2

lemma equation_759 : (A 27 3 + A 27 17) + (A 23 3 + A 27 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 3

lemma equation_761 : (A 27 5 + A 27 9) + (A 23 5 + A 27 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 5

lemma equation_763 : (A 27 7 + A 27 11) + (A 23 7 + A 27 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 7

lemma equation_764 : (A 27 4 + A 27 8) + (A 23 8 + A 27 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 8

lemma equation_766 : (A 27 6 + A 27 10) + (A 23 10 + A 27 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 10

lemma equation_768 : (A 27 12) + (A 23 12 + A 27 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 12

lemma equation_769 : (A 27 13) + (A 23 13 + A 27 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 13

lemma equation_770 : (A 27 14) + (A 23 14 + A 27 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 14

lemma equation_771 : (A 27 15) + (A 23 15 + A 27 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 15

lemma equation_772 : (A 27 16) + (A 23 16 + A 27 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 16

lemma equation_774 : (A 27 1 + A 27 17 + A 27 18) + (A 23 18 + A 27 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 18

lemma equation_775 : (A 27 19) + (A 23 19 + A 27 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 19

lemma equation_778 : (A 27 22 + A 27 26) + (A 23 22 + A 27 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 22

lemma equation_779 : (A 27 23 + A 27 27) + (A 23 23 + A 27 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 23

lemma equation_780 : (A 27 20 + A 27 24) + (A 23 24 + A 27 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 24

lemma equation_781 : (A 27 21 + A 27 25) + (A 23 25 + A 27 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 0 27 25

lemma equation_784 : (A 0 0 + A 0 18) + (A 0 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 0

lemma equation_788 : (A 0 4 + A 0 8) + (A 0 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 4

lemma equation_790 : (A 0 6 + A 0 10) + (A 0 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 6

lemma equation_793 : (A 0 5 + A 0 9) + (A 0 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 9

lemma equation_795 : (A 0 7 + A 0 11) + (A 0 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 11

lemma equation_804 : (A 0 20 + A 0 24) + (A 0 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 20

lemma equation_805 : (A 0 21 + A 0 25) + (A 0 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 21

lemma equation_810 : (A 0 22 + A 0 26) + (A 0 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 26

lemma equation_811 : (A 0 23 + A 0 27) + (A 0 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 0 27

lemma equation_812 : (A 1 0 + A 1 18) + (A 1 0 + A 17 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 0

lemma equation_813 : (A 1 1) + (A 1 1 + A 17 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 1

lemma equation_814 : (A 1 2 + A 1 18) + (A 1 2 + A 17 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 2

lemma equation_815 : (A 1 3 + A 1 18) + (A 1 3 + A 17 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 3

lemma equation_816 : (A 1 4 + A 1 8) + (A 1 4 + A 17 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 4

lemma equation_817 : (A 1 5) + (A 1 5 + A 17 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 5

lemma equation_818 : (A 1 6 + A 1 10) + (A 1 6 + A 17 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 6

lemma equation_819 : (A 1 7) + (A 1 7 + A 17 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 7

lemma equation_820 : (A 1 8) + (A 1 8 + A 17 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 8

lemma equation_821 : (A 1 5 + A 1 9) + (A 1 9 + A 17 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 9

lemma equation_822 : (A 1 10) + (A 1 10 + A 17 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 10

lemma equation_823 : (A 1 7 + A 1 11) + (A 1 11 + A 17 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 11

lemma equation_824 : (A 1 12) + (A 1 12 + A 17 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 12

lemma equation_825 : (A 1 13) + (A 1 13 + A 17 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 13

lemma equation_826 : (A 1 14) + (A 1 14 + A 17 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 14

lemma equation_827 : (A 1 15) + (A 1 15 + A 17 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 15

lemma equation_828 : (A 1 16) + (A 1 16 + A 17 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 16

lemma equation_829 : (A 1 1 + A 1 17 + A 1 18) + (A 1 17 + A 17 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 17

lemma equation_830 : (A 1 18) + (A 1 18 + A 17 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 18

lemma equation_831 : (A 1 19) + (A 1 19 + A 17 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 19

lemma equation_832 : (A 1 20 + A 1 24) + (A 1 20 + A 17 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 20

lemma equation_833 : (A 1 21 + A 1 25) + (A 1 21 + A 17 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 21

lemma equation_834 : (A 1 22) + (A 1 22 + A 17 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 22

lemma equation_835 : (A 1 23) + (A 1 23 + A 17 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 23

lemma equation_836 : (A 1 24) + (A 1 24 + A 17 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 24

lemma equation_837 : (A 1 25) + (A 1 25 + A 17 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 25

lemma equation_838 : (A 1 22 + A 1 26) + (A 1 26 + A 17 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 26

lemma equation_839 : (A 1 23 + A 1 27) + (A 1 27 + A 17 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 1 27

lemma equation_840 : (A 2 0 + A 2 18) + (A 2 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 0

lemma equation_844 : (A 2 4 + A 2 8) + (A 2 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 4

lemma equation_846 : (A 2 6 + A 2 10) + (A 2 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 6

lemma equation_849 : (A 2 5 + A 2 9) + (A 2 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 9

lemma equation_851 : (A 2 7 + A 2 11) + (A 2 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 11

lemma equation_860 : (A 2 20 + A 2 24) + (A 2 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 20

lemma equation_861 : (A 2 21 + A 2 25) + (A 2 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 21

lemma equation_866 : (A 2 22 + A 2 26) + (A 2 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 26

lemma equation_867 : (A 2 23 + A 2 27) + (A 2 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 2 27

lemma equation_868 : (A 3 0 + A 3 18) + (A 3 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 0

lemma equation_872 : (A 3 4 + A 3 8) + (A 3 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 4

lemma equation_874 : (A 3 6 + A 3 10) + (A 3 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 6

lemma equation_877 : (A 3 5 + A 3 9) + (A 3 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 9

lemma equation_879 : (A 3 7 + A 3 11) + (A 3 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 11

lemma equation_888 : (A 3 20 + A 3 24) + (A 3 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 20

lemma equation_889 : (A 3 21 + A 3 25) + (A 3 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 21

lemma equation_894 : (A 3 22 + A 3 26) + (A 3 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 26

lemma equation_895 : (A 3 23 + A 3 27) + (A 3 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 3 27

lemma equation_896 : (A 4 0 + A 4 18) + (A 4 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 0

lemma equation_900 : (A 4 4 + A 4 8) + (A 4 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 4

lemma equation_902 : (A 4 6 + A 4 10) + (A 4 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 6

lemma equation_905 : (A 4 5 + A 4 9) + (A 4 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 9

lemma equation_907 : (A 4 7 + A 4 11) + (A 4 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 11

lemma equation_913 : (A 4 1 + A 4 17 + A 4 18) + (A 4 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 17

lemma equation_916 : (A 4 20 + A 4 24) + (A 4 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 20

lemma equation_917 : (A 4 21 + A 4 25) + (A 4 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 21

lemma equation_922 : (A 4 22 + A 4 26) + (A 4 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 26

lemma equation_923 : (A 4 23 + A 4 27) + (A 4 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 4 27

lemma equation_924 : (A 5 0 + A 5 18) + (A 5 0 + A 9 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 0

lemma equation_925 : (A 5 1) + (A 5 1 + A 9 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 1

lemma equation_926 : (A 5 2 + A 5 18) + (A 5 2 + A 9 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 2

lemma equation_927 : (A 5 3 + A 5 18) + (A 5 3 + A 9 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 3

lemma equation_929 : (A 5 5) + (A 5 5 + A 9 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 5

lemma equation_931 : (A 5 7) + (A 5 7 + A 9 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 7

lemma equation_932 : (A 5 8) + (A 5 8 + A 9 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 8

lemma equation_934 : (A 5 10) + (A 5 10 + A 9 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 10

lemma equation_936 : (A 5 12) + (A 5 12 + A 9 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 12

lemma equation_937 : (A 5 13) + (A 5 13 + A 9 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 13

lemma equation_938 : (A 5 14) + (A 5 14 + A 9 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 14

lemma equation_939 : (A 5 15) + (A 5 15 + A 9 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 15

lemma equation_940 : (A 5 16) + (A 5 16 + A 9 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 16

lemma equation_942 : (A 5 18) + (A 5 18 + A 9 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 18

lemma equation_943 : (A 5 19) + (A 5 19 + A 9 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 19

lemma equation_946 : (A 5 22) + (A 5 22 + A 9 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 22

lemma equation_947 : (A 5 23) + (A 5 23 + A 9 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 23

lemma equation_948 : (A 5 24) + (A 5 24 + A 9 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 24

lemma equation_949 : (A 5 25) + (A 5 25 + A 9 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 5 25

lemma equation_952 : (A 6 0 + A 6 18) + (A 6 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 0

lemma equation_956 : (A 6 4 + A 6 8) + (A 6 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 4

lemma equation_958 : (A 6 6 + A 6 10) + (A 6 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 6

lemma equation_961 : (A 6 5 + A 6 9) + (A 6 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 9

lemma equation_963 : (A 6 7 + A 6 11) + (A 6 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 11

lemma equation_969 : (A 6 1 + A 6 17 + A 6 18) + (A 6 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 17

lemma equation_972 : (A 6 20 + A 6 24) + (A 6 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 20

lemma equation_973 : (A 6 21 + A 6 25) + (A 6 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 21

lemma equation_978 : (A 6 22 + A 6 26) + (A 6 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 26

lemma equation_979 : (A 6 23 + A 6 27) + (A 6 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 6 27

lemma equation_980 : (A 7 0 + A 7 18) + (A 7 0 + A 11 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 0

lemma equation_981 : (A 7 1) + (A 7 1 + A 11 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 1

lemma equation_982 : (A 7 2 + A 7 18) + (A 7 2 + A 11 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 2

lemma equation_983 : (A 7 3 + A 7 18) + (A 7 3 + A 11 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 3

lemma equation_985 : (A 7 5) + (A 7 5 + A 11 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 5

lemma equation_987 : (A 7 7) + (A 7 7 + A 11 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 7

lemma equation_988 : (A 7 8) + (A 7 8 + A 11 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 8

lemma equation_990 : (A 7 10) + (A 7 10 + A 11 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 10

lemma equation_992 : (A 7 12) + (A 7 12 + A 11 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 12

lemma equation_993 : (A 7 13) + (A 7 13 + A 11 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 13

lemma equation_994 : (A 7 14) + (A 7 14 + A 11 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 14

lemma equation_995 : (A 7 15) + (A 7 15 + A 11 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 15

lemma equation_996 : (A 7 16) + (A 7 16 + A 11 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 16

lemma equation_998 : (A 7 18) + (A 7 18 + A 11 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 18

lemma equation_999 : (A 7 19) + (A 7 19 + A 11 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 19

lemma equation_1002 : (A 7 22) + (A 7 22 + A 11 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 22

lemma equation_1003 : (A 7 23) + (A 7 23 + A 11 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 23

lemma equation_1004 : (A 7 24) + (A 7 24 + A 11 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 24

lemma equation_1005 : (A 7 25) + (A 7 25 + A 11 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 7 25

lemma equation_1008 : (A 8 0 + A 8 18) + (A 4 0 + A 8 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 0

lemma equation_1010 : (A 8 2 + A 8 18) + (A 4 2 + A 8 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 2

lemma equation_1011 : (A 8 3 + A 8 18) + (A 4 3 + A 8 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 3

lemma equation_1020 : (A 8 12) + (A 4 12 + A 8 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 12

lemma equation_1021 : (A 8 13) + (A 4 13 + A 8 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 13

lemma equation_1022 : (A 8 14) + (A 4 14 + A 8 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 14

lemma equation_1023 : (A 8 15) + (A 4 15 + A 8 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 15

lemma equation_1024 : (A 8 16) + (A 4 16 + A 8 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 16

lemma equation_1027 : (A 8 19) + (A 4 19 + A 8 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 8 19

lemma equation_1064 : (A 10 0 + A 10 18) + (A 6 0 + A 10 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 0

lemma equation_1066 : (A 10 2 + A 10 18) + (A 6 2 + A 10 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 2

lemma equation_1067 : (A 10 3 + A 10 18) + (A 6 3 + A 10 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 3

lemma equation_1076 : (A 10 12) + (A 6 12 + A 10 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 12

lemma equation_1077 : (A 10 13) + (A 6 13 + A 10 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 13

lemma equation_1078 : (A 10 14) + (A 6 14 + A 10 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 14

lemma equation_1079 : (A 10 15) + (A 6 15 + A 10 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 15

lemma equation_1080 : (A 10 16) + (A 6 16 + A 10 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 16

lemma equation_1083 : (A 10 19) + (A 6 19 + A 10 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 10 19

lemma equation_1120 : (A 12 0 + A 12 18) + (A 12 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 0

lemma equation_1124 : (A 12 4 + A 12 8) + (A 12 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 4

lemma equation_1126 : (A 12 6 + A 12 10) + (A 12 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 6

lemma equation_1129 : (A 12 5 + A 12 9) + (A 12 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 9

lemma equation_1131 : (A 12 7 + A 12 11) + (A 12 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 11

lemma equation_1140 : (A 12 20 + A 12 24) + (A 12 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 20

lemma equation_1141 : (A 12 21 + A 12 25) + (A 12 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 21

lemma equation_1146 : (A 12 22 + A 12 26) + (A 12 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 26

lemma equation_1147 : (A 12 23 + A 12 27) + (A 12 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 12 27

lemma equation_1148 : (A 13 0 + A 13 18) + (A 13 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 0

lemma equation_1152 : (A 13 4 + A 13 8) + (A 13 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 4

lemma equation_1154 : (A 13 6 + A 13 10) + (A 13 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 6

lemma equation_1157 : (A 13 5 + A 13 9) + (A 13 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 9

lemma equation_1159 : (A 13 7 + A 13 11) + (A 13 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 11

lemma equation_1168 : (A 13 20 + A 13 24) + (A 13 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 20

lemma equation_1169 : (A 13 21 + A 13 25) + (A 13 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 21

lemma equation_1174 : (A 13 22 + A 13 26) + (A 13 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 26

lemma equation_1175 : (A 13 23 + A 13 27) + (A 13 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 13 27

lemma equation_1176 : (A 14 0 + A 14 18) + (A 14 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 0

lemma equation_1180 : (A 14 4 + A 14 8) + (A 14 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 4

lemma equation_1182 : (A 14 6 + A 14 10) + (A 14 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 6

lemma equation_1185 : (A 14 5 + A 14 9) + (A 14 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 9

lemma equation_1187 : (A 14 7 + A 14 11) + (A 14 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 11

lemma equation_1196 : (A 14 20 + A 14 24) + (A 14 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 20

lemma equation_1197 : (A 14 21 + A 14 25) + (A 14 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 21

lemma equation_1202 : (A 14 22 + A 14 26) + (A 14 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 26

lemma equation_1203 : (A 14 23 + A 14 27) + (A 14 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 14 27

lemma equation_1204 : (A 15 0 + A 15 18) + (A 15 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 0

lemma equation_1208 : (A 15 4 + A 15 8) + (A 15 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 4

lemma equation_1210 : (A 15 6 + A 15 10) + (A 15 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 6

lemma equation_1213 : (A 15 5 + A 15 9) + (A 15 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 9

lemma equation_1215 : (A 15 7 + A 15 11) + (A 15 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 11

lemma equation_1224 : (A 15 20 + A 15 24) + (A 15 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 20

lemma equation_1225 : (A 15 21 + A 15 25) + (A 15 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 21

lemma equation_1230 : (A 15 22 + A 15 26) + (A 15 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 26

lemma equation_1231 : (A 15 23 + A 15 27) + (A 15 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 15 27

lemma equation_1232 : (A 16 0 + A 16 18) + (A 16 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 0

lemma equation_1236 : (A 16 4 + A 16 8) + (A 16 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 4

lemma equation_1238 : (A 16 6 + A 16 10) + (A 16 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 6

lemma equation_1241 : (A 16 5 + A 16 9) + (A 16 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 9

lemma equation_1243 : (A 16 7 + A 16 11) + (A 16 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 11

lemma equation_1252 : (A 16 20 + A 16 24) + (A 16 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 20

lemma equation_1253 : (A 16 21 + A 16 25) + (A 16 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 21

lemma equation_1258 : (A 16 22 + A 16 26) + (A 16 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 26

lemma equation_1259 : (A 16 23 + A 16 27) + (A 16 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 16 27

lemma equation_1316 : (A 19 0 + A 19 18) + (A 19 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 0

lemma equation_1320 : (A 19 4 + A 19 8) + (A 19 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 4

lemma equation_1322 : (A 19 6 + A 19 10) + (A 19 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 6

lemma equation_1325 : (A 19 5 + A 19 9) + (A 19 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 9

lemma equation_1327 : (A 19 7 + A 19 11) + (A 19 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 11

lemma equation_1336 : (A 19 20 + A 19 24) + (A 19 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 20

lemma equation_1337 : (A 19 21 + A 19 25) + (A 19 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 21

lemma equation_1342 : (A 19 22 + A 19 26) + (A 19 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 26

lemma equation_1343 : (A 19 23 + A 19 27) + (A 19 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 19 27

lemma equation_1344 : (A 20 0 + A 20 18) + (A 20 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 0

lemma equation_1348 : (A 20 4 + A 20 8) + (A 20 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 4

lemma equation_1350 : (A 20 6 + A 20 10) + (A 20 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 6

lemma equation_1353 : (A 20 5 + A 20 9) + (A 20 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 9

lemma equation_1355 : (A 20 7 + A 20 11) + (A 20 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 11

lemma equation_1361 : (A 20 1 + A 20 17 + A 20 18) + (A 20 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 17

lemma equation_1364 : (A 20 20 + A 20 24) + (A 20 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 20

lemma equation_1365 : (A 20 21 + A 20 25) + (A 20 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 21

lemma equation_1370 : (A 20 22 + A 20 26) + (A 20 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 26

lemma equation_1371 : (A 20 23 + A 20 27) + (A 20 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 20 27

lemma equation_1372 : (A 21 0 + A 21 18) + (A 21 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 0

lemma equation_1376 : (A 21 4 + A 21 8) + (A 21 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 4

lemma equation_1378 : (A 21 6 + A 21 10) + (A 21 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 6

lemma equation_1381 : (A 21 5 + A 21 9) + (A 21 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 9

lemma equation_1383 : (A 21 7 + A 21 11) + (A 21 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 11

lemma equation_1389 : (A 21 1 + A 21 17 + A 21 18) + (A 21 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 17

lemma equation_1392 : (A 21 20 + A 21 24) + (A 21 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 20

lemma equation_1393 : (A 21 21 + A 21 25) + (A 21 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 21

lemma equation_1398 : (A 21 22 + A 21 26) + (A 21 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 26

lemma equation_1399 : (A 21 23 + A 21 27) + (A 21 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 21 27

lemma equation_1400 : (A 22 0 + A 22 18) + (A 22 0 + A 26 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 0

lemma equation_1401 : (A 22 1) + (A 22 1 + A 26 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 1

lemma equation_1402 : (A 22 2 + A 22 18) + (A 22 2 + A 26 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 2

lemma equation_1403 : (A 22 3 + A 22 18) + (A 22 3 + A 26 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 3

lemma equation_1405 : (A 22 5) + (A 22 5 + A 26 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 5

lemma equation_1407 : (A 22 7) + (A 22 7 + A 26 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 7

lemma equation_1408 : (A 22 8) + (A 22 8 + A 26 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 8

lemma equation_1410 : (A 22 10) + (A 22 10 + A 26 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 10

lemma equation_1412 : (A 22 12) + (A 22 12 + A 26 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 12

lemma equation_1413 : (A 22 13) + (A 22 13 + A 26 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 13

lemma equation_1414 : (A 22 14) + (A 22 14 + A 26 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 14

lemma equation_1415 : (A 22 15) + (A 22 15 + A 26 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 15

lemma equation_1416 : (A 22 16) + (A 22 16 + A 26 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 16

lemma equation_1418 : (A 22 18) + (A 22 18 + A 26 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 18

lemma equation_1419 : (A 22 19) + (A 22 19 + A 26 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 19

lemma equation_1422 : (A 22 22) + (A 22 22 + A 26 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 22

lemma equation_1423 : (A 22 23) + (A 22 23 + A 26 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 23

lemma equation_1424 : (A 22 24) + (A 22 24 + A 26 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 24

lemma equation_1425 : (A 22 25) + (A 22 25 + A 26 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 22 25

lemma equation_1428 : (A 23 0 + A 23 18) + (A 23 0 + A 27 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 0

lemma equation_1429 : (A 23 1) + (A 23 1 + A 27 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 1

lemma equation_1430 : (A 23 2 + A 23 18) + (A 23 2 + A 27 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 2

lemma equation_1431 : (A 23 3 + A 23 18) + (A 23 3 + A 27 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 3

lemma equation_1433 : (A 23 5) + (A 23 5 + A 27 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 5

lemma equation_1435 : (A 23 7) + (A 23 7 + A 27 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 7

lemma equation_1436 : (A 23 8) + (A 23 8 + A 27 8) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 8

lemma equation_1438 : (A 23 10) + (A 23 10 + A 27 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 10

lemma equation_1440 : (A 23 12) + (A 23 12 + A 27 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 12

lemma equation_1441 : (A 23 13) + (A 23 13 + A 27 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 13

lemma equation_1442 : (A 23 14) + (A 23 14 + A 27 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 14

lemma equation_1443 : (A 23 15) + (A 23 15 + A 27 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 15

lemma equation_1444 : (A 23 16) + (A 23 16 + A 27 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 16

lemma equation_1446 : (A 23 18) + (A 23 18 + A 27 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 18

lemma equation_1447 : (A 23 19) + (A 23 19 + A 27 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 19

lemma equation_1450 : (A 23 22) + (A 23 22 + A 27 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 22

lemma equation_1451 : (A 23 23) + (A 23 23 + A 27 23) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 23

lemma equation_1452 : (A 23 24) + (A 23 24 + A 27 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 24

lemma equation_1453 : (A 23 25) + (A 23 25 + A 27 25) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 23 25

lemma equation_1456 : (A 24 0 + A 24 18) + (A 20 0 + A 24 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 0

lemma equation_1458 : (A 24 2 + A 24 18) + (A 20 2 + A 24 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 2

lemma equation_1459 : (A 24 3 + A 24 18) + (A 20 3 + A 24 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 3

lemma equation_1468 : (A 24 12) + (A 20 12 + A 24 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 12

lemma equation_1469 : (A 24 13) + (A 20 13 + A 24 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 13

lemma equation_1470 : (A 24 14) + (A 20 14 + A 24 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 14

lemma equation_1471 : (A 24 15) + (A 20 15 + A 24 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 15

lemma equation_1472 : (A 24 16) + (A 20 16 + A 24 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 16

lemma equation_1475 : (A 24 19) + (A 20 19 + A 24 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 24 19

lemma equation_1484 : (A 25 0 + A 25 18) + (A 21 0 + A 25 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 0

lemma equation_1486 : (A 25 2 + A 25 18) + (A 21 2 + A 25 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 2

lemma equation_1487 : (A 25 3 + A 25 18) + (A 21 3 + A 25 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 3

lemma equation_1496 : (A 25 12) + (A 21 12 + A 25 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 12

lemma equation_1497 : (A 25 13) + (A 21 13 + A 25 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 13

lemma equation_1498 : (A 25 14) + (A 21 14 + A 25 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 14

lemma equation_1499 : (A 25 15) + (A 21 15 + A 25 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 15

lemma equation_1500 : (A 25 16) + (A 21 16 + A 25 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 16

lemma equation_1503 : (A 25 19) + (A 21 19 + A 25 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 1 25 19

lemma equation_1568 : (A 0 0) + (A 0 0 + A 6 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 0

lemma equation_1572 : (A 0 4) + (A 0 4 + A 6 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 4

lemma equation_1574 : (A 0 0 + A 0 5 + A 0 6) + (A 0 6 + A 6 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 6

lemma equation_1577 : (A 0 8 + A 0 9 + A 0 12 + A 0 13) + (A 0 9 + A 6 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 9

lemma equation_1579 : (A 0 10 + A 0 11 + A 0 14 + A 0 15 + A 0 18 + A 0 19 + A 0 22 + A 0 23) + (A 0 11 + A 6 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 11

lemma equation_1585 : (A 0 8 + A 0 9 + A 0 12 + A 0 13 + A 0 16 + A 0 17 + A 0 20 + A 0 21) + (A 0 17 + A 6 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 17

lemma equation_1588 : (A 0 8 + A 0 12 + A 0 16 + A 0 20) + (A 0 20 + A 6 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 20

lemma equation_1589 : (A 0 8 + A 0 13 + A 0 16 + A 0 21) + (A 0 21 + A 6 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 21

lemma equation_1594 : (A 0 2 + A 0 25 + A 0 26) + (A 0 26 + A 6 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 26

lemma equation_1595 : (A 0 3 + A 0 24 + A 0 27) + (A 0 27 + A 6 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 0 27

lemma equation_1597 : (A 1 1 + A 1 5 + A 1 24 + A 1 25) + (A 1 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 1

lemma equation_1602 : (A 1 0 + A 1 5 + A 1 6) + (A 1 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 6

lemma equation_1605 : (A 1 8 + A 1 9 + A 1 12 + A 1 13) + (A 1 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 9

lemma equation_1606 : (A 1 10 + A 1 18) + (A 1 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 10

lemma equation_1607 : (A 1 10 + A 1 11 + A 1 14 + A 1 15 + A 1 18 + A 1 19 + A 1 22 + A 1 23) + (A 1 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 11

lemma equation_1608 : (A 1 8 + A 1 12) + (A 1 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 12

lemma equation_1610 : (A 1 10 + A 1 14 + A 1 18 + A 1 22) + (A 1 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 14

lemma equation_1611 : (A 1 10 + A 1 15 + A 1 18 + A 1 23) + (A 1 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 15

lemma equation_1613 : (A 1 8 + A 1 9 + A 1 12 + A 1 13 + A 1 16 + A 1 17 + A 1 20 + A 1 21) + (A 1 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 17

lemma equation_1616 : (A 1 8 + A 1 12 + A 1 16 + A 1 20) + (A 1 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 20

lemma equation_1622 : (A 1 2 + A 1 25 + A 1 26) + (A 1 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 26

lemma equation_1623 : (A 1 3 + A 1 24 + A 1 27) + (A 1 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 1 27

lemma equation_1624 : (A 2 0) + (A 2 0 + A 26 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 0

lemma equation_1628 : (A 2 4) + (A 2 4 + A 26 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 4

lemma equation_1630 : (A 2 0 + A 2 5 + A 2 6) + (A 2 6 + A 26 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 6

lemma equation_1633 : (A 2 8 + A 2 9 + A 2 12 + A 2 13) + (A 2 9 + A 26 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 9

lemma equation_1635 : (A 2 10 + A 2 11 + A 2 14 + A 2 15 + A 2 18 + A 2 19 + A 2 22 + A 2 23) + (A 2 11 + A 26 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 11

lemma equation_1641 : (A 2 8 + A 2 9 + A 2 12 + A 2 13 + A 2 16 + A 2 17 + A 2 20 + A 2 21) + (A 2 17 + A 26 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 17

lemma equation_1644 : (A 2 8 + A 2 12 + A 2 16 + A 2 20) + (A 2 20 + A 26 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 20

lemma equation_1645 : (A 2 8 + A 2 13 + A 2 16 + A 2 21) + (A 2 21 + A 26 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 21

lemma equation_1650 : (A 2 2 + A 2 25 + A 2 26) + (A 2 26 + A 26 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 26

lemma equation_1651 : (A 2 3 + A 2 24 + A 2 27) + (A 2 27 + A 26 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 2 27

lemma equation_1652 : (A 3 0) + (A 3 0 + A 27 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 0

lemma equation_1656 : (A 3 4) + (A 3 4 + A 27 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 4

lemma equation_1658 : (A 3 0 + A 3 5 + A 3 6) + (A 3 6 + A 27 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 6

lemma equation_1661 : (A 3 8 + A 3 9 + A 3 12 + A 3 13) + (A 3 9 + A 27 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 9

lemma equation_1663 : (A 3 10 + A 3 11 + A 3 14 + A 3 15 + A 3 18 + A 3 19 + A 3 22 + A 3 23) + (A 3 11 + A 27 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 11

lemma equation_1672 : (A 3 8 + A 3 12 + A 3 16 + A 3 20) + (A 3 20 + A 27 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 20

lemma equation_1673 : (A 3 8 + A 3 13 + A 3 16 + A 3 21) + (A 3 21 + A 27 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 21

lemma equation_1678 : (A 3 2 + A 3 25 + A 3 26) + (A 3 26 + A 27 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 26

lemma equation_1679 : (A 3 3 + A 3 24 + A 3 27) + (A 3 27 + A 27 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 3 27

lemma equation_1686 : (A 4 0 + A 4 5 + A 4 6) + (A 4 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 4 6

lemma equation_1697 : (A 4 8 + A 4 9 + A 4 12 + A 4 13 + A 4 16 + A 4 17 + A 4 20 + A 4 21) + (A 4 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 4 17

lemma equation_1708 : (A 5 0) + (A 1 0 + A 5 0 + A 6 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 0

lemma equation_1709 : (A 5 1 + A 5 5 + A 5 24 + A 5 25) + (A 1 1 + A 5 1 + A 6 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 1

lemma equation_1710 : (A 5 2) + (A 1 2 + A 5 2 + A 6 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 2

lemma equation_1714 : (A 5 0 + A 5 5 + A 5 6) + (A 1 6 + A 5 6 + A 6 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 6

lemma equation_1715 : (A 5 7) + (A 1 7 + A 5 7 + A 6 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 7

lemma equation_1717 : (A 5 8 + A 5 9 + A 5 12 + A 5 13) + (A 1 9 + A 5 9 + A 6 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 9

lemma equation_1718 : (A 5 10 + A 5 18) + (A 1 10 + A 5 10 + A 6 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 10

lemma equation_1719 : (A 5 10 + A 5 11 + A 5 14 + A 5 15 + A 5 18 + A 5 19 + A 5 22 + A 5 23) + (A 1 11 + A 5 11 + A 6 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 11

lemma equation_1720 : (A 5 8 + A 5 12) + (A 1 12 + A 5 12 + A 6 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 12

lemma equation_1722 : (A 5 10 + A 5 14 + A 5 18 + A 5 22) + (A 1 14 + A 5 14 + A 6 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 14

lemma equation_1723 : (A 5 10 + A 5 15 + A 5 18 + A 5 23) + (A 1 15 + A 5 15 + A 6 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 15

lemma equation_1728 : (A 5 8 + A 5 12 + A 5 16 + A 5 20) + (A 1 20 + A 5 20 + A 6 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 20

lemma equation_1734 : (A 5 2 + A 5 25 + A 5 26) + (A 1 26 + A 5 26 + A 6 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 26

lemma equation_1735 : (A 5 3 + A 5 24 + A 5 27) + (A 1 27 + A 5 27 + A 6 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 5 27

lemma equation_1765 : (A 7 1 + A 7 5 + A 7 24 + A 7 25) + (A 7 1) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 1

lemma equation_1770 : (A 7 0 + A 7 5 + A 7 6) + (A 7 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 6

lemma equation_1773 : (A 7 8 + A 7 9 + A 7 12 + A 7 13) + (A 7 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 9

lemma equation_1774 : (A 7 10 + A 7 18) + (A 7 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 10

lemma equation_1775 : (A 7 10 + A 7 11 + A 7 14 + A 7 15 + A 7 18 + A 7 19 + A 7 22 + A 7 23) + (A 7 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 11

lemma equation_1778 : (A 7 10 + A 7 14 + A 7 18 + A 7 22) + (A 7 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 14

lemma equation_1779 : (A 7 10 + A 7 15 + A 7 18 + A 7 23) + (A 7 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 15

lemma equation_1790 : (A 7 2 + A 7 25 + A 7 26) + (A 7 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 7 26

lemma equation_1792 : (A 8 0) + (A 8 0 + A 9 0 + A 12 0 + A 13 0 + A 16 0 + A 17 0 + A 20 0 + A 21 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 0

lemma equation_1794 : (A 8 2) + (A 8 2 + A 9 2 + A 12 2 + A 13 2 + A 16 2 + A 17 2 + A 20 2 + A 21 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 2

lemma equation_1795 : (A 8 3) + (A 8 3 + A 9 3 + A 12 3 + A 13 3 + A 16 3 + A 17 3 + A 20 3 + A 21 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 3

lemma equation_1796 : (A 8 4) + (A 8 4 + A 9 4 + A 12 4 + A 13 4 + A 16 4 + A 17 4 + A 20 4 + A 21 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 4

lemma equation_1798 : (A 8 0 + A 8 5 + A 8 6) + (A 8 6 + A 9 6 + A 12 6 + A 13 6 + A 16 6 + A 17 6 + A 20 6 + A 21 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 6

lemma equation_1801 : (A 8 8 + A 8 9 + A 8 12 + A 8 13) + (A 8 9 + A 9 9 + A 12 9 + A 13 9 + A 16 9 + A 17 9 + A 20 9 + A 21 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 9

lemma equation_1803 : (A 8 10 + A 8 11 + A 8 14 + A 8 15 + A 8 18 + A 8 19 + A 8 22 + A 8 23) + (A 8 11 + A 9 11 + A 12 11 + A 13 11 + A 16 11 + A 17 11 + A 20 11 + A 21 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 11

lemma equation_1804 : (A 8 8 + A 8 12) + (A 8 12 + A 9 12 + A 12 12 + A 13 12 + A 16 12 + A 17 12 + A 20 12 + A 21 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 12

lemma equation_1805 : (A 8 8 + A 8 13) + (A 8 13 + A 9 13 + A 12 13 + A 13 13 + A 16 13 + A 17 13 + A 20 13 + A 21 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 13

lemma equation_1806 : (A 8 10 + A 8 14 + A 8 18 + A 8 22) + (A 8 14 + A 9 14 + A 12 14 + A 13 14 + A 16 14 + A 17 14 + A 20 14 + A 21 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 14

lemma equation_1807 : (A 8 10 + A 8 15 + A 8 18 + A 8 23) + (A 8 15 + A 9 15 + A 12 15 + A 13 15 + A 16 15 + A 17 15 + A 20 15 + A 21 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 15

lemma equation_1808 : (A 8 8 + A 8 16) + (A 8 16 + A 9 16 + A 12 16 + A 13 16 + A 16 16 + A 17 16 + A 20 16 + A 21 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 16

lemma equation_1809 : (A 8 8 + A 8 9 + A 8 12 + A 8 13 + A 8 16 + A 8 17 + A 8 20 + A 8 21) + (A 8 17 + A 9 17 + A 12 17 + A 13 17 + A 16 17 + A 17 17 + A 20 17 + A 21 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 17

lemma equation_1811 : (A 8 18 + A 8 19 + A 8 22 + A 8 23) + (A 8 19 + A 9 19 + A 12 19 + A 13 19 + A 16 19 + A 17 19 + A 20 19 + A 21 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 19

lemma equation_1812 : (A 8 8 + A 8 12 + A 8 16 + A 8 20) + (A 8 20 + A 9 20 + A 12 20 + A 13 20 + A 16 20 + A 17 20 + A 20 20 + A 21 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 20

lemma equation_1813 : (A 8 8 + A 8 13 + A 8 16 + A 8 21) + (A 8 21 + A 9 21 + A 12 21 + A 13 21 + A 16 21 + A 17 21 + A 20 21 + A 21 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 21

lemma equation_1818 : (A 8 2 + A 8 25 + A 8 26) + (A 8 26 + A 9 26 + A 12 26 + A 13 26 + A 16 26 + A 17 26 + A 20 26 + A 21 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 26

lemma equation_1819 : (A 8 3 + A 8 24 + A 8 27) + (A 8 27 + A 9 27 + A 12 27 + A 13 27 + A 16 27 + A 17 27 + A 20 27 + A 21 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 8 27

lemma equation_1848 : (A 10 0) + (A 10 0 + A 11 0 + A 14 0 + A 15 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 0

lemma equation_1850 : (A 10 2) + (A 10 2 + A 11 2 + A 14 2 + A 15 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 2

lemma equation_1851 : (A 10 3) + (A 10 3 + A 11 3 + A 14 3 + A 15 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 3

lemma equation_1859 : (A 10 10 + A 10 11 + A 10 14 + A 10 15 + A 10 18 + A 10 19 + A 10 22 + A 10 23) + (A 10 11 + A 11 11 + A 14 11 + A 15 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 11

lemma equation_1860 : (A 10 8 + A 10 12) + (A 10 12 + A 11 12 + A 14 12 + A 15 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 12

lemma equation_1861 : (A 10 8 + A 10 13) + (A 10 13 + A 11 13 + A 14 13 + A 15 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 13

lemma equation_1862 : (A 10 10 + A 10 14 + A 10 18 + A 10 22) + (A 10 14 + A 11 14 + A 14 14 + A 15 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 14

lemma equation_1863 : (A 10 10 + A 10 15 + A 10 18 + A 10 23) + (A 10 15 + A 11 15 + A 14 15 + A 15 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 15

lemma equation_1864 : (A 10 8 + A 10 16) + (A 10 16 + A 11 16 + A 14 16 + A 15 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 16

lemma equation_1867 : (A 10 18 + A 10 19 + A 10 22 + A 10 23) + (A 10 19 + A 11 19 + A 14 19 + A 15 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 10 19

lemma equation_1904 : (A 12 0) + (A 9 0 + A 12 0 + A 17 0 + A 20 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 0

lemma equation_1908 : (A 12 4) + (A 9 4 + A 12 4 + A 17 4 + A 20 4) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 4

lemma equation_1910 : (A 12 0 + A 12 5 + A 12 6) + (A 9 6 + A 12 6 + A 17 6 + A 20 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 6

lemma equation_1913 : (A 12 8 + A 12 9 + A 12 12 + A 12 13) + (A 9 9 + A 12 9 + A 17 9 + A 20 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 9

lemma equation_1915 : (A 12 10 + A 12 11 + A 12 14 + A 12 15 + A 12 18 + A 12 19 + A 12 22 + A 12 23) + (A 9 11 + A 12 11 + A 17 11 + A 20 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 11

lemma equation_1921 : (A 12 8 + A 12 9 + A 12 12 + A 12 13 + A 12 16 + A 12 17 + A 12 20 + A 12 21) + (A 9 17 + A 12 17 + A 17 17 + A 20 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 17

lemma equation_1924 : (A 12 8 + A 12 12 + A 12 16 + A 12 20) + (A 9 20 + A 12 20 + A 17 20 + A 20 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 20

lemma equation_1925 : (A 12 8 + A 12 13 + A 12 16 + A 12 21) + (A 9 21 + A 12 21 + A 17 21 + A 20 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 21

lemma equation_1930 : (A 12 2 + A 12 25 + A 12 26) + (A 9 26 + A 12 26 + A 17 26 + A 20 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 26

lemma equation_1931 : (A 12 3 + A 12 24 + A 12 27) + (A 9 27 + A 12 27 + A 17 27 + A 20 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 12 27

lemma equation_1932 : (A 13 0) + (A 9 0 + A 13 0 + A 17 0 + A 21 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 0

lemma equation_1938 : (A 13 0 + A 13 5 + A 13 6) + (A 9 6 + A 13 6 + A 17 6 + A 21 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 6

lemma equation_1941 : (A 13 8 + A 13 9 + A 13 12 + A 13 13) + (A 9 9 + A 13 9 + A 17 9 + A 21 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 9

lemma equation_1943 : (A 13 10 + A 13 11 + A 13 14 + A 13 15 + A 13 18 + A 13 19 + A 13 22 + A 13 23) + (A 9 11 + A 13 11 + A 17 11 + A 21 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 11

lemma equation_1949 : (A 13 8 + A 13 9 + A 13 12 + A 13 13 + A 13 16 + A 13 17 + A 13 20 + A 13 21) + (A 9 17 + A 13 17 + A 17 17 + A 21 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 17

lemma equation_1952 : (A 13 8 + A 13 12 + A 13 16 + A 13 20) + (A 9 20 + A 13 20 + A 17 20 + A 21 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 20

lemma equation_1953 : (A 13 8 + A 13 13 + A 13 16 + A 13 21) + (A 9 21 + A 13 21 + A 17 21 + A 21 21) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 21

lemma equation_1958 : (A 13 2 + A 13 25 + A 13 26) + (A 9 26 + A 13 26 + A 17 26 + A 21 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 26

lemma equation_1959 : (A 13 3 + A 13 24 + A 13 27) + (A 9 27 + A 13 27 + A 17 27 + A 21 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 13 27

lemma equation_1966 : (A 14 0 + A 14 5 + A 14 6) + (A 11 6 + A 14 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 6

lemma equation_1969 : (A 14 8 + A 14 9 + A 14 12 + A 14 13) + (A 11 9 + A 14 9) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 9

lemma equation_1971 : (A 14 10 + A 14 11 + A 14 14 + A 14 15 + A 14 18 + A 14 19 + A 14 22 + A 14 23) + (A 11 11 + A 14 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 11

lemma equation_1977 : (A 14 8 + A 14 9 + A 14 12 + A 14 13 + A 14 16 + A 14 17 + A 14 20 + A 14 21) + (A 11 17 + A 14 17) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 17

lemma equation_1980 : (A 14 8 + A 14 12 + A 14 16 + A 14 20) + (A 11 20 + A 14 20) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 20

lemma equation_1986 : (A 14 2 + A 14 25 + A 14 26) + (A 11 26 + A 14 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 26

lemma equation_1987 : (A 14 3 + A 14 24 + A 14 27) + (A 11 27 + A 14 27) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 14 27

lemma equation_2072 : (A 18 0) + (A 10 0 + A 11 0 + A 14 0 + A 15 0 + A 18 0 + A 19 0 + A 22 0 + A 23 0) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 0

lemma equation_2074 : (A 18 2) + (A 10 2 + A 11 2 + A 14 2 + A 15 2 + A 18 2 + A 19 2 + A 22 2 + A 23 2) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 2

lemma equation_2075 : (A 18 3) + (A 10 3 + A 11 3 + A 14 3 + A 15 3 + A 18 3 + A 19 3 + A 22 3 + A 23 3) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 3

lemma equation_2084 : (A 18 8 + A 18 12) + (A 10 12 + A 11 12 + A 14 12 + A 15 12 + A 18 12 + A 19 12 + A 22 12 + A 23 12) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 12

lemma equation_2085 : (A 18 8 + A 18 13) + (A 10 13 + A 11 13 + A 14 13 + A 15 13 + A 18 13 + A 19 13 + A 22 13 + A 23 13) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 13

lemma equation_2086 : (A 18 10 + A 18 14 + A 18 18 + A 18 22) + (A 10 14 + A 11 14 + A 14 14 + A 15 14 + A 18 14 + A 19 14 + A 22 14 + A 23 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 14

lemma equation_2087 : (A 18 10 + A 18 15 + A 18 18 + A 18 23) + (A 10 15 + A 11 15 + A 14 15 + A 15 15 + A 18 15 + A 19 15 + A 22 15 + A 23 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 15

lemma equation_2088 : (A 18 8 + A 18 16) + (A 10 16 + A 11 16 + A 14 16 + A 15 16 + A 18 16 + A 19 16 + A 22 16 + A 23 16) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 16

lemma equation_2091 : (A 18 18 + A 18 19 + A 18 22 + A 18 23) + (A 10 19 + A 11 19 + A 14 19 + A 15 19 + A 18 19 + A 19 19 + A 22 19 + A 23 19) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 18 19

lemma equation_2190 : (A 22 0 + A 22 5 + A 22 6) + (A 11 6 + A 14 6 + A 19 6 + A 22 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 22 6

lemma equation_2195 : (A 22 10 + A 22 11 + A 22 14 + A 22 15 + A 22 18 + A 22 19 + A 22 22 + A 22 23) + (A 11 11 + A 14 11 + A 19 11 + A 22 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 22 11

lemma equation_2198 : (A 22 10 + A 22 14 + A 22 18 + A 22 22) + (A 11 14 + A 14 14 + A 19 14 + A 22 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 22 14

lemma equation_2199 : (A 22 10 + A 22 15 + A 22 18 + A 22 23) + (A 11 15 + A 14 15 + A 19 15 + A 22 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 22 15

lemma equation_2210 : (A 22 2 + A 22 25 + A 22 26) + (A 11 26 + A 14 26 + A 19 26 + A 22 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 22 26

lemma equation_2246 : (A 24 0 + A 24 5 + A 24 6) + (A 1 6 + A 24 6 + A 27 6) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 24 6

lemma equation_2251 : (A 24 10 + A 24 11 + A 24 14 + A 24 15 + A 24 18 + A 24 19 + A 24 22 + A 24 23) + (A 1 11 + A 24 11 + A 27 11) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 24 11

lemma equation_2254 : (A 24 10 + A 24 14 + A 24 18 + A 24 22) + (A 1 14 + A 24 14 + A 27 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 24 14

lemma equation_2255 : (A 24 10 + A 24 15 + A 24 18 + A 24 23) + (A 1 15 + A 24 15 + A 27 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 24 15

lemma equation_2266 : (A 24 2 + A 24 25 + A 24 26) + (A 1 26 + A 24 26 + A 27 26) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 24 26

lemma equation_2282 : (A 25 10 + A 25 14 + A 25 18 + A 25 22) + (A 1 14 + A 25 14 + A 26 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 25 14

lemma equation_2283 : (A 25 10 + A 25 15 + A 25 18 + A 25 23) + (A 1 15 + A 25 15 + A 26 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 2 25 15

lemma equation_2359 : (A 0 7) + (A 0 7 + A 5 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 0 7

lemma equation_2362 : (A 0 10 + A 0 11 + A 0 14 + A 0 15) + (A 0 10 + A 5 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 0 10

lemma equation_2370 : (A 0 10 + A 0 11 + A 0 14 + A 0 15 + A 0 18 + A 0 19 + A 0 22 + A 0 23) + (A 0 18 + A 5 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 0 18

lemma equation_2374 : (A 0 11 + A 0 14 + A 0 19 + A 0 22) + (A 0 22 + A 5 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 0 22

lemma equation_2390 : (A 1 10 + A 1 11 + A 1 14 + A 1 15) + (A 1 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 1 10

lemma equation_2402 : (A 1 11 + A 1 14 + A 1 19 + A 1 22) + (A 1 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 1 22

lemma equation_2415 : (A 2 7) + (A 2 7 + A 25 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 2 7

lemma equation_2418 : (A 2 10 + A 2 11 + A 2 14 + A 2 15) + (A 2 10 + A 25 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 2 10

lemma equation_2426 : (A 2 10 + A 2 11 + A 2 14 + A 2 15 + A 2 18 + A 2 19 + A 2 22 + A 2 23) + (A 2 18 + A 25 18) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 2 18

lemma equation_2430 : (A 2 11 + A 2 14 + A 2 19 + A 2 22) + (A 2 22 + A 25 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 2 22

lemma equation_2443 : (A 3 7) + (A 3 7 + A 24 7) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 3 7

lemma equation_2469 : (A 4 0 + A 4 5 + A 4 6) + (A 4 5) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 4 5

lemma equation_2474 : (A 4 10 + A 4 11 + A 4 14 + A 4 15) + (A 4 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 4 10

lemma equation_2488 : (A 4 3 + A 4 24 + A 4 27) + (A 4 24) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 4 24

lemma equation_2618 : (A 9 11 + A 9 14) + (A 8 14 + A 9 14 + A 12 14 + A 13 14) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 9 14

lemma equation_2619 : (A 9 11 + A 9 15) + (A 8 15 + A 9 15 + A 12 15 + A 13 15) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 9 15

lemma equation_2698 : (A 12 10 + A 12 11 + A 12 14 + A 12 15) + (A 8 10 + A 12 10) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 12 10

lemma equation_2710 : (A 12 11 + A 12 14 + A 12 19 + A 12 22) + (A 8 22 + A 12 22) = 0 := by
  simpa [constantCols, constantRows, add_assoc] using constant_equation A h 3 12 22

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
