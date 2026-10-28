module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Data

/-!
# Checked small matrix products for the literal words

These witnesses use the literal ATLAS words, the published characteristic-two
basis and the recipes in SylowTwoPart/source/candidate.json. Numerical
equalities are proved by the kernel; source attribution is in Model.Data and
SymmetricLinear.Model.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality

set_option maxRecDepth 2000 in
theorem conjugate10_left : decode (qRows.get 10) * decode (firstRows) = decode (conjugateStep10) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate10_right : decode (firstRows) * decode (qRows.get 11) = decode (conjugateStep10) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate11_left : decode (qRows.get 11) * decode (secondRows) = decode (conjugateStep11) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate11_right : decode (secondRows) * decode (qRows.get 12) = decode (conjugateStep11) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate12_left : decode (qRows.get 12) * decode (firstRows) = decode (conjugateStep12) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate12_right : decode (firstRows) * decode (qRows.get 13) = decode (conjugateStep12) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate13_left : decode (qRows.get 13) * decode (secondRows) = decode (conjugateStep13) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate13_right : decode (secondRows) * decode (qRows.get 14) = decode (conjugateStep13) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate14_left : decode (qRows.get 14) * decode (firstRows) = decode (conjugateStep14) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem conjugate14_right : decode (firstRows) * decode (qRows.get 15) = decode (conjugateStep14) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word1_step0 : decode (qRows.get 2) * decode (wordRows.get 0) = decode (wordRows.get 1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word2_step0 : decode (qRows.get 3) * decode (wordRows.get 0) = decode (wordRows.get 2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word3_step0 : decode (qRows.get 4) * decode (wordRows.get 0) = decode (wordRows.get 3) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word4_step0 : decode (qRows.get 5) * decode (wordRows.get 1) = decode (wordRows.get 4) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word5_step0 : decode (qRows.get 6) * decode (wordRows.get 2) = decode (wordRows.get 5) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word6_step0 : decode (qRows.get 7) * decode (wordRows.get 3) = decode (wordRows.get 6) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word7_step0 : decode (qRows.get 8) * decode (wordRows.get 0) = decode (wordStep7_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word7_step1 : decode (wordStep7_0) * decode (wordRows.get 2) = decode (wordRows.get 7) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word8_step0 : decode (qRows.get 9) * decode (wordRows.get 0) = decode (wordStep8_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word8_step1 : decode (wordStep8_0) * decode (wordRows.get 2) = decode (wordStep8_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word8_step2 : decode (wordStep8_1) * decode (wordRows.get 7) = decode (wordStep8_2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word8_step3 : decode (wordStep8_2) * decode (wordRows.get 4) = decode (wordRows.get 8) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word9_step0 : decode (qRows.get 10) * decode (wordRows.get 7) = decode (wordRows.get 9) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word10_step0 : decode (qRows.get 11) * decode (wordRows.get 0) = decode (wordStep10_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word10_step1 : decode (wordStep10_0) * decode (wordRows.get 7) = decode (wordStep10_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word10_step2 : decode (wordStep10_1) * decode (wordRows.get 9) = decode (wordRows.get 10) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word11_step0 : decode (qRows.get 12) * decode (wordRows.get 7) = decode (wordStep11_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word11_step1 : decode (wordStep11_0) * decode (wordRows.get 5) = decode (wordStep11_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word11_step2 : decode (wordStep11_1) * decode (wordRows.get 4) = decode (wordStep11_2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word11_step3 : decode (wordStep11_2) * decode (wordRows.get 9) = decode (wordRows.get 11) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word12_step0 : decode (qRows.get 13) * decode (wordRows.get 0) = decode (wordStep12_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word12_step1 : decode (wordStep12_0) * decode (wordRows.get 9) = decode (wordStep12_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word12_step2 : decode (wordStep12_1) * decode (wordRows.get 8) = decode (wordStep12_2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word12_step3 : decode (wordStep12_2) * decode (wordRows.get 6) = decode (wordRows.get 12) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step0 : decode (qRows.get 14) * decode (wordRows.get 3) = decode (wordStep13_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step1 : decode (wordStep13_0) * decode (wordRows.get 1) = decode (wordStep13_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step2 : decode (wordStep13_1) * decode (wordRows.get 7) = decode (wordStep13_2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step3 : decode (wordStep13_2) * decode (wordRows.get 5) = decode (wordStep13_3) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step4 : decode (wordStep13_3) * decode (wordRows.get 9) = decode (wordStep13_4) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step5 : decode (wordStep13_4) * decode (wordRows.get 8) = decode (wordStep13_5) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word13_step6 : decode (wordStep13_5) * decode (wordRows.get 6) = decode (wordRows.get 13) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step0 : decode (qRows.get 15) * decode (wordRows.get 2) = decode (wordStep14_0) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step1 : decode (wordStep14_0) * decode (wordRows.get 1) = decode (wordStep14_1) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step2 : decode (wordStep14_1) * decode (wordRows.get 7) = decode (wordStep14_2) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step3 : decode (wordStep14_2) * decode (wordRows.get 5) = decode (wordStep14_3) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step4 : decode (wordStep14_3) * decode (wordRows.get 4) = decode (wordStep14_4) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step5 : decode (wordStep14_4) * decode (wordRows.get 9) = decode (wordStep14_5) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step6 : decode (wordStep14_5) * decode (wordRows.get 8) = decode (wordStep14_6) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step7 : decode (wordStep14_6) * decode (wordRows.get 6) = decode (wordStep14_7) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step8 : decode (wordStep14_7) * decode (wordRows.get 13) = decode (wordStep14_8) :=
  product _ _ _ (by decide +kernel)

set_option maxRecDepth 2000 in
theorem word14_step9 : decode (wordStep14_8) * decode (wordRows.get 10) = decode (wordRows.get 14) :=
  product _ _ _ (by decide +kernel)

end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
