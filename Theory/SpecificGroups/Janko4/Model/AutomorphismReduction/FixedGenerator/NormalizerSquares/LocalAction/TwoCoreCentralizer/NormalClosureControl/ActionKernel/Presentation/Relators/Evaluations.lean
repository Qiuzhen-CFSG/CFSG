module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products01
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products02
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products03
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products04
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products05
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products07
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products08
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products09
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products10
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products11
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products12
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products13
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products14
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products15
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products16
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products17
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products18
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products19
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products20
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products21
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products22

/-!
# Certified lifts of the max2 quotient relators

Shared subwords factor the explicit words in `Presentation.Data`. The original
ATLAS max2 matrices and thirteen normal-closure generators are already checked
in `CentralizerReduction`. Each additional product is checked by kernel reduction
of the proved packed arithmetic; Python supplies witnesses only. The resulting
relator lifts are actual words in the relative normal closure, with no local
identification or order assumed. See `Presentation/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

lemma eval_x : wordEval x = decodeRows xRows :=
  (wordEval_positive false).trans representation_x
lemma eval_y : wordEval y = decodeRows yRows :=
  (wordEval_positive true).trans representation_y
lemma eval_xi : wordEval xi = decodeRows xRows :=
  wordEval_negative false representation_x
    ((decoded_product product_1).trans decode_packedOne)
lemma eval_yi : wordEval yi = decodeRows r0Rows :=
  wordEval_negative true representation_y
    ((decoded_product product_2).trans decode_packedOne)

lemma eval_w0 : wordEval w0 = decodeRows r1Rows :=
  wordEval_product eval_x eval_yi product_3

lemma eval_w1 : wordEval w1 = decodeRows r2Rows :=
  wordEval_product eval_x eval_y product_4

lemma eval_w2 : wordEval w2 = decodeRows r3Rows :=
  wordEval_product eval_w1 eval_w0 product_5

lemma eval_w3 : wordEval w3 = decodeRows r4Rows :=
  wordEval_product eval_w1 eval_w2 product_6

lemma eval_w4 : wordEval w4 = decodeRows r5Rows :=
  wordEval_product eval_w0 eval_w0 product_7

lemma eval_w5 : wordEval w5 = decodeRows r6Rows :=
  wordEval_product eval_w1 eval_w3 product_8

lemma eval_w6 : wordEval w6 = decodeRows r7Rows :=
  wordEval_product eval_w2 eval_w4 product_9

lemma eval_w7 : wordEval w7 = decodeRows r8Rows :=
  wordEval_product eval_w0 eval_w3 product_10

lemma eval_w8 : wordEval w8 = decodeRows r9Rows :=
  wordEval_product eval_w2 eval_w2 product_11

lemma eval_w9 : wordEval w9 = decodeRows r10Rows :=
  wordEval_product eval_w1 eval_w5 product_12

lemma eval_w10 : wordEval w10 = decodeRows r11Rows :=
  wordEval_product eval_w1 eval_w9 product_13

lemma eval_w11 : wordEval w11 = decodeRows r12Rows :=
  wordEval_product eval_w3 eval_w4 product_14

lemma eval_w12 : wordEval w12 = decodeRows r13Rows :=
  wordEval_product eval_w6 eval_w5 product_15

lemma eval_w13 : wordEval w13 = decodeRows r14Rows :=
  wordEval_product eval_w0 eval_w2 product_16

lemma eval_w14 : wordEval w14 = decodeRows r15Rows :=
  wordEval_product eval_w7 eval_w2 product_17

lemma eval_w15 : wordEval w15 = decodeRows r16Rows :=
  wordEval_product eval_w6 eval_w4 product_18

lemma eval_w16 : wordEval w16 = decodeRows r17Rows :=
  wordEval_product eval_w2 eval_w0 product_19

lemma eval_w17 : wordEval w17 = decodeRows r18Rows :=
  wordEval_product eval_w11 eval_w4 product_20

lemma eval_w18 : wordEval w18 = decodeRows r19Rows :=
  wordEval_product eval_w13 eval_w7 product_21

lemma eval_w19 : wordEval w19 = decodeRows r20Rows :=
  wordEval_product eval_w8 eval_w11 product_22

lemma eval_w20 : wordEval w20 = decodeRows r21Rows :=
  wordEval_product eval_w5 eval_w4 product_23

lemma eval_w21 : wordEval w21 = decodeRows r22Rows :=
  wordEval_product eval_w3 eval_w12 product_24

lemma eval_w22 : wordEval w22 = decodeRows r23Rows :=
  wordEval_product eval_w17 eval_w19 product_25

lemma eval_w23 : wordEval w23 = decodeRows r24Rows :=
  wordEval_product eval_w4 eval_w4 product_26

lemma eval_w24 : wordEval w24 = decodeRows r25Rows :=
  wordEval_product eval_w1 eval_w10 product_27

lemma eval_w25 : wordEval w25 = decodeRows r26Rows :=
  wordEval_product eval_w14 eval_w22 product_28

lemma eval_w26 : wordEval w26 = decodeRows r27Rows :=
  wordEval_product eval_w0 eval_w12 product_29

lemma eval_w27 : wordEval w27 = decodeRows r28Rows :=
  wordEval_product eval_w8 eval_w2 product_30

lemma eval_w28 : wordEval w28 = decodeRows r29Rows :=
  wordEval_product eval_w27 eval_w20 product_31

lemma eval_w29 : wordEval w29 = decodeRows r30Rows :=
  wordEval_product eval_w28 eval_w10 product_32

lemma eval_w30 : wordEval w30 = decodeRows r31Rows :=
  wordEval_product eval_w0 eval_w8 product_33

lemma eval_w31 : wordEval w31 = decodeRows r32Rows :=
  wordEval_product eval_w6 eval_w2 product_34

lemma eval_w32 : wordEval w32 = decodeRows r33Rows :=
  wordEval_product eval_w8 eval_w0 product_35

lemma eval_w33 : wordEval w33 = decodeRows r34Rows :=
  wordEval_product eval_w0 eval_w5 product_36

lemma eval_w34 : wordEval w34 = decodeRows r35Rows :=
  wordEval_product eval_w3 eval_w6 product_37

lemma eval_w35 : wordEval w35 = decodeRows r36Rows :=
  wordEval_product eval_w1 eval_w1 product_38

lemma eval_w36 : wordEval w36 = decodeRows r37Rows :=
  wordEval_product eval_w18 eval_w5 product_39

lemma eval_w37 : wordEval w37 = decodeRows r38Rows :=
  wordEval_product eval_w3 eval_w3 product_40

lemma eval_w38 : wordEval w38 = decodeRows r39Rows :=
  wordEval_product eval_w29 eval_w6 product_41

lemma eval_w39 : wordEval w39 = decodeRows r40Rows :=
  wordEval_product eval_w9 eval_w2 product_42

lemma eval_w40 : wordEval w40 = decodeRows r41Rows :=
  wordEval_product eval_w7 eval_w36 product_43

lemma eval_w41 : wordEval w41 = decodeRows r42Rows :=
  wordEval_product eval_w34 eval_w3 product_44

lemma eval_w42 : wordEval w42 = decodeRows r43Rows :=
  wordEval_product eval_w26 eval_w2 product_45

lemma eval_w43 : wordEval w43 = decodeRows r44Rows :=
  wordEval_product eval_w25 eval_w14 product_46

lemma eval_w44 : wordEval w44 = decodeRows r45Rows :=
  wordEval_product eval_w32 eval_w9 product_47

lemma eval_w45 : wordEval w45 = decodeRows r46Rows :=
  wordEval_product eval_w25 eval_w7 product_48

lemma eval_w46 : wordEval w46 = decodeRows r47Rows :=
  wordEval_product eval_w7 eval_w12 product_49

lemma eval_w47 : wordEval w47 = decodeRows r48Rows :=
  wordEval_product eval_w21 eval_w3 product_50

lemma eval_w48 : wordEval w48 = decodeRows r49Rows :=
  wordEval_product eval_w10 eval_w4 product_51

lemma eval_w49 : wordEval w49 = decodeRows r50Rows :=
  wordEval_product eval_w2 eval_w13 product_52

lemma eval_w50 : wordEval w50 = decodeRows r51Rows :=
  wordEval_product eval_w21 eval_w10 product_53

lemma eval_w51 : wordEval w51 = decodeRows r52Rows :=
  wordEval_product eval_w16 eval_w15 product_54

lemma eval_w52 : wordEval w52 = decodeRows r53Rows :=
  wordEval_product eval_w16 eval_w31 product_55

lemma eval_w53 : wordEval w53 = decodeRows r54Rows :=
  wordEval_product eval_w7 eval_w38 product_56

lemma eval_w54 : wordEval w54 = decodeRows r55Rows :=
  wordEval_product eval_w44 eval_w30 product_57

lemma eval_w55 : wordEval w55 = decodeRows r56Rows :=
  wordEval_product eval_w54 eval_w10 product_58

lemma eval_w56 : wordEval w56 = decodeRows r57Rows :=
  wordEval_product eval_w9 eval_w4 product_59

lemma eval_w57 : wordEval w57 = decodeRows r58Rows :=
  wordEval_product eval_w0 eval_w15 product_60

lemma eval_w58 : wordEval w58 = decodeRows r59Rows :=
  wordEval_product eval_w5 eval_w15 product_61

lemma eval_w59 : wordEval w59 = decodeRows r60Rows :=
  wordEval_product eval_w58 eval_w20 product_62

lemma eval_w60 : wordEval w60 = decodeRows r61Rows :=
  wordEval_product eval_w59 eval_w8 product_63

lemma eval_w61 : wordEval w61 = decodeRows r62Rows :=
  wordEval_product eval_w60 eval_w8 product_64

lemma eval_w62 : wordEval w62 = decodeRows packedOne :=
  wordEval_product eval_x eval_x product_1

lemma eval_w63 : wordEval w63 = decodeRows r0Rows :=
  wordEval_product eval_y eval_y product_0

lemma eval_w64 : wordEval w64 = decodeRows packedOne :=
  wordEval_product eval_y eval_w63 product_2

lemma eval_w65 : wordEval w65 = decodeRows r63Rows :=
  wordEval_product eval_w23 eval_w23 product_65

lemma eval_w66 : wordEval w66 = decodeRows r64Rows :=
  wordEval_product eval_w23 eval_w4 product_66

lemma eval_w67 : wordEval w67 = decodeRows packedOne :=
  wordEval_product eval_w65 eval_w66 product_67

lemma eval_w68 : wordEval w68 = decodeRows r65Rows :=
  wordEval_product eval_w2 eval_w18 product_68

lemma eval_w69 : wordEval w69 = decodeRows r66Rows :=
  wordEval_product eval_w3 eval_w68 product_69

lemma eval_w70 : wordEval w70 = decodeRows r67Rows :=
  wordEval_product eval_w3 eval_w24 product_70

lemma eval_w71 : wordEval w71 = decodeRows r68Rows :=
  wordEval_product eval_w19 eval_w1 product_71

lemma eval_w72 : wordEval w72 = decodeRows r69Rows :=
  wordEval_product eval_w70 eval_w71 product_72

lemma eval_w73 : wordEval w73 = decodeRows r70Rows :=
  wordEval_product eval_w69 eval_w72 product_73

lemma eval_w74 : wordEval w74 = decodeRows r71Rows :=
  wordEval_product eval_w26 eval_w17 product_74

lemma eval_w75 : wordEval w75 = decodeRows r72Rows :=
  wordEval_product eval_w16 eval_w10 product_75

lemma eval_w76 : wordEval w76 = decodeRows r73Rows :=
  wordEval_product eval_w21 eval_w75 product_76

lemma eval_w77 : wordEval w77 = decodeRows r74Rows :=
  wordEval_product eval_w74 eval_w76 product_77

lemma eval_w78 : wordEval w78 = decodeRows r75Rows :=
  wordEval_product eval_w2 eval_w47 product_78

lemma eval_w79 : wordEval w79 = decodeRows r76Rows :=
  wordEval_product eval_y eval_w78 product_79

lemma eval_w80 : wordEval w80 = decodeRows r77Rows :=
  wordEval_product eval_w47 eval_w47 product_80

lemma eval_w81 : wordEval w81 = decodeRows r78Rows :=
  wordEval_product eval_w21 eval_x product_81

lemma eval_w82 : wordEval w82 = decodeRows r79Rows :=
  wordEval_product eval_w80 eval_w81 product_82

lemma eval_w83 : wordEval w83 = decodeRows r80Rows :=
  wordEval_product eval_w79 eval_w82 product_83

lemma eval_w84 : wordEval w84 = decodeRows r81Rows :=
  wordEval_product eval_w24 eval_w3 product_84

lemma eval_w85 : wordEval w85 = decodeRows r82Rows :=
  wordEval_product eval_w32 eval_w84 product_85

lemma eval_w86 : wordEval w86 = decodeRows r83Rows :=
  wordEval_product eval_w12 eval_w2 product_86

lemma eval_w87 : wordEval w87 = decodeRows r84Rows :=
  wordEval_product eval_w33 eval_w86 product_87

lemma eval_w88 : wordEval w88 = decodeRows r85Rows :=
  wordEval_product eval_w85 eval_w87 product_88

lemma eval_w89 : wordEval w89 = decodeRows r86Rows :=
  wordEval_product eval_w11 eval_w5 product_89

lemma eval_w90 : wordEval w90 = decodeRows r87Rows :=
  wordEval_product eval_w12 eval_w89 product_90

lemma eval_w91 : wordEval w91 = decodeRows r88Rows :=
  wordEval_product eval_w2 eval_w35 product_91

lemma eval_w92 : wordEval w92 = decodeRows r89Rows :=
  wordEval_product eval_w24 eval_w91 product_92

lemma eval_w93 : wordEval w93 = decodeRows r90Rows :=
  wordEval_product eval_w90 eval_w92 product_93

lemma eval_w94 : wordEval w94 = decodeRows r91Rows :=
  wordEval_product eval_w88 eval_w93 product_94

lemma eval_w95 : wordEval w95 = decodeRows r92Rows :=
  wordEval_product eval_w18 eval_w36 product_95

lemma eval_w96 : wordEval w96 = decodeRows r93Rows :=
  wordEval_product eval_w34 eval_w39 product_96

lemma eval_w97 : wordEval w97 = decodeRows r94Rows :=
  wordEval_product eval_w95 eval_w96 product_97

lemma eval_w98 : wordEval w98 = decodeRows r95Rows :=
  wordEval_product eval_w40 eval_w34 product_98

lemma eval_w99 : wordEval w99 = decodeRows r96Rows :=
  wordEval_product eval_w35 eval_w35 product_99

lemma eval_w100 : wordEval w100 = decodeRows r97Rows :=
  wordEval_product eval_w98 eval_w99 product_100

lemma eval_w101 : wordEval w101 = decodeRows r98Rows :=
  wordEval_product eval_w97 eval_w100 product_101

lemma eval_w102 : wordEval w102 = decodeRows r99Rows :=
  wordEval_product eval_w3 eval_w11 product_102

lemma eval_w103 : wordEval w103 = decodeRows r100Rows :=
  wordEval_product eval_w33 eval_w40 product_103

lemma eval_w104 : wordEval w104 = decodeRows r101Rows :=
  wordEval_product eval_w3 eval_w103 product_104

lemma eval_w105 : wordEval w105 = decodeRows r102Rows :=
  wordEval_product eval_w102 eval_w104 product_105

lemma eval_w106 : wordEval w106 = decodeRows r103Rows :=
  wordEval_product eval_w41 eval_w48 product_106

lemma eval_w107 : wordEval w107 = decodeRows r104Rows :=
  wordEval_product eval_w49 eval_w1 product_107

lemma eval_w108 : wordEval w108 = decodeRows r105Rows :=
  wordEval_product eval_w33 eval_w107 product_108

lemma eval_w109 : wordEval w109 = decodeRows r106Rows :=
  wordEval_product eval_w106 eval_w108 product_109

lemma eval_w110 : wordEval w110 = decodeRows r107Rows :=
  wordEval_product eval_w105 eval_w109 product_110

lemma eval_w111 : wordEval w111 = decodeRows r108Rows :=
  wordEval_product eval_w50 eval_w42 product_111

lemma eval_w112 : wordEval w112 = decodeRows r109Rows :=
  wordEval_product eval_w5 eval_w111 product_112

lemma eval_w113 : wordEval w113 = decodeRows r110Rows :=
  wordEval_product eval_w112 eval_w112 product_113

lemma eval_w114 : wordEval w114 = decodeRows r111Rows :=
  wordEval_product eval_w7 eval_w29 product_114

lemma eval_w115 : wordEval w115 = decodeRows r112Rows :=
  wordEval_product eval_w51 eval_w2 product_115

lemma eval_w116 : wordEval w116 = decodeRows r113Rows :=
  wordEval_product eval_w114 eval_w115 product_116

lemma eval_w117 : wordEval w117 = decodeRows r114Rows :=
  wordEval_product eval_w3 eval_w29 product_117

lemma eval_w118 : wordEval w118 = decodeRows r115Rows :=
  wordEval_product eval_w51 eval_w1 product_118

lemma eval_w119 : wordEval w119 = decodeRows r116Rows :=
  wordEval_product eval_w117 eval_w118 product_119

lemma eval_w120 : wordEval w120 = decodeRows r117Rows :=
  wordEval_product eval_w116 eval_w119 product_120

lemma eval_w121 : wordEval w121 = decodeRows r118Rows :=
  wordEval_product eval_w7 eval_w30 product_121

lemma eval_w122 : wordEval w122 = decodeRows r119Rows :=
  wordEval_product eval_w40 eval_w21 product_122

lemma eval_w123 : wordEval w123 = decodeRows r120Rows :=
  wordEval_product eval_w5 eval_w122 product_123

lemma eval_w124 : wordEval w124 = decodeRows r121Rows :=
  wordEval_product eval_w121 eval_w123 product_124

lemma eval_w125 : wordEval w125 = decodeRows r122Rows :=
  wordEval_product eval_w16 eval_w20 product_125

lemma eval_w126 : wordEval w126 = decodeRows r123Rows :=
  wordEval_product eval_w37 eval_w125 product_126

lemma eval_w127 : wordEval w127 = decodeRows r124Rows :=
  wordEval_product eval_w16 eval_w9 product_127

lemma eval_w128 : wordEval w128 = decodeRows r125Rows :=
  wordEval_product eval_w5 eval_w127 product_128

lemma eval_w129 : wordEval w129 = decodeRows r126Rows :=
  wordEval_product eval_w126 eval_w128 product_129

lemma eval_w130 : wordEval w130 = decodeRows r127Rows :=
  wordEval_product eval_w124 eval_w129 product_130

lemma eval_w131 : wordEval w131 = decodeRows r128Rows :=
  wordEval_product eval_w4 eval_w3 product_131

lemma eval_w132 : wordEval w132 = decodeRows r129Rows :=
  wordEval_product eval_w24 eval_w33 product_132

lemma eval_w133 : wordEval w133 = decodeRows r130Rows :=
  wordEval_product eval_w38 eval_w132 product_133

lemma eval_w134 : wordEval w134 = decodeRows r131Rows :=
  wordEval_product eval_w131 eval_w133 product_134

lemma eval_w135 : wordEval w135 = decodeRows r132Rows :=
  wordEval_product eval_w52 eval_w7 product_135

lemma eval_w136 : wordEval w136 = decodeRows r133Rows :=
  wordEval_product eval_w7 eval_w24 product_136

lemma eval_w137 : wordEval w137 = decodeRows r134Rows :=
  wordEval_product eval_w3 eval_w136 product_137

lemma eval_w138 : wordEval w138 = decodeRows r135Rows :=
  wordEval_product eval_w135 eval_w137 product_138

lemma eval_w139 : wordEval w139 = decodeRows r136Rows :=
  wordEval_product eval_w134 eval_w138 product_139

lemma eval_w140 : wordEval w140 = decodeRows r137Rows :=
  wordEval_product eval_w38 eval_w48 product_140

lemma eval_w141 : wordEval w141 = decodeRows r138Rows :=
  wordEval_product eval_w18 eval_w140 product_141

lemma eval_w142 : wordEval w142 = decodeRows r139Rows :=
  wordEval_product eval_w2 eval_w53 product_142

lemma eval_w143 : wordEval w143 = decodeRows r140Rows :=
  wordEval_product eval_w10 eval_w0 product_143

lemma eval_w144 : wordEval w144 = decodeRows r141Rows :=
  wordEval_product eval_w142 eval_w143 product_144

lemma eval_w145 : wordEval w145 = decodeRows r142Rows :=
  wordEval_product eval_w141 eval_w144 product_145

lemma eval_w146 : wordEval w146 = decodeRows r143Rows :=
  wordEval_product eval_y eval_w2 product_146

lemma eval_w147 : wordEval w147 = decodeRows r144Rows :=
  wordEval_product eval_w43 eval_w12 product_147

lemma eval_w148 : wordEval w148 = decodeRows r145Rows :=
  wordEval_product eval_w146 eval_w147 product_148

lemma eval_w149 : wordEval w149 = decodeRows r146Rows :=
  wordEval_product eval_w43 eval_w6 product_149

lemma eval_w150 : wordEval w150 = decodeRows r147Rows :=
  wordEval_product eval_w1 eval_x product_150

lemma eval_w151 : wordEval w151 = decodeRows r148Rows :=
  wordEval_product eval_w149 eval_w150 product_151

lemma eval_w152 : wordEval w152 = decodeRows r149Rows :=
  wordEval_product eval_w148 eval_w151 product_152

lemma eval_w153 : wordEval w153 = decodeRows r150Rows :=
  wordEval_product eval_w6 eval_w13 product_153

lemma eval_w154 : wordEval w154 = decodeRows r151Rows :=
  wordEval_product eval_w5 eval_w153 product_154

lemma eval_w155 : wordEval w155 = decodeRows r152Rows :=
  wordEval_product eval_w42 eval_w21 product_155

lemma eval_w156 : wordEval w156 = decodeRows r153Rows :=
  wordEval_product eval_w41 eval_w155 product_156

lemma eval_w157 : wordEval w157 = decodeRows r154Rows :=
  wordEval_product eval_w154 eval_w156 product_157

lemma eval_w158 : wordEval w158 = decodeRows r155Rows :=
  wordEval_product eval_w13 eval_w33 product_158

lemma eval_w159 : wordEval w159 = decodeRows r156Rows :=
  wordEval_product eval_w11 eval_w158 product_159

lemma eval_w160 : wordEval w160 = decodeRows r157Rows :=
  wordEval_product eval_w6 eval_w3 product_160

lemma eval_w161 : wordEval w161 = decodeRows r158Rows :=
  wordEval_product eval_w26 eval_w35 product_161

lemma eval_w162 : wordEval w162 = decodeRows r159Rows :=
  wordEval_product eval_w160 eval_w161 product_162

lemma eval_w163 : wordEval w163 = decodeRows r160Rows :=
  wordEval_product eval_w159 eval_w162 product_163

lemma eval_w164 : wordEval w164 = decodeRows r161Rows :=
  wordEval_product eval_w157 eval_w163 product_164

lemma eval_w165 : wordEval w165 = decodeRows r162Rows :=
  wordEval_product eval_w6 eval_w0 product_165

lemma eval_w166 : wordEval w166 = decodeRows r163Rows :=
  wordEval_product eval_w0 eval_w165 product_166

lemma eval_w167 : wordEval w167 = decodeRows r164Rows :=
  wordEval_product eval_w26 eval_w15 product_167

lemma eval_w168 : wordEval w168 = decodeRows r165Rows :=
  wordEval_product eval_w48 eval_w167 product_168

lemma eval_w169 : wordEval w169 = decodeRows r166Rows :=
  wordEval_product eval_w166 eval_w168 product_169

lemma eval_w170 : wordEval w170 = decodeRows r167Rows :=
  wordEval_product eval_w5 eval_w75 product_170

lemma eval_w171 : wordEval w171 = decodeRows r168Rows :=
  wordEval_product eval_w30 eval_w14 product_171

lemma eval_w172 : wordEval w172 = decodeRows r169Rows :=
  wordEval_product eval_w55 eval_w171 product_172

lemma eval_w173 : wordEval w173 = decodeRows r170Rows :=
  wordEval_product eval_w170 eval_w172 product_173

lemma eval_w174 : wordEval w174 = decodeRows r171Rows :=
  wordEval_product eval_w169 eval_w173 product_174

lemma eval_w175 : wordEval w175 = decodeRows r172Rows :=
  wordEval_product eval_w42 eval_w3 product_175

lemma eval_w176 : wordEval w176 = decodeRows r173Rows :=
  wordEval_product eval_w41 eval_w175 product_176

lemma eval_w177 : wordEval w177 = decodeRows r174Rows :=
  wordEval_product eval_w44 eval_w13 product_177

lemma eval_w178 : wordEval w178 = decodeRows r175Rows :=
  wordEval_product eval_w5 eval_w177 product_178

lemma eval_w179 : wordEval w179 = decodeRows r176Rows :=
  wordEval_product eval_w176 eval_w178 product_179

lemma eval_w180 : wordEval w180 = decodeRows r177Rows :=
  wordEval_product eval_w56 eval_w10 product_180

lemma eval_w181 : wordEval w181 = decodeRows r178Rows :=
  wordEval_product eval_w17 eval_w180 product_181

lemma eval_w182 : wordEval w182 = decodeRows r179Rows :=
  wordEval_product eval_w6 eval_w10 product_182

lemma eval_w183 : wordEval w183 = decodeRows r180Rows :=
  wordEval_product eval_w23 eval_w1 product_183

lemma eval_w184 : wordEval w184 = decodeRows r181Rows :=
  wordEval_product eval_w182 eval_w183 product_184

lemma eval_w185 : wordEval w185 = decodeRows r182Rows :=
  wordEval_product eval_w181 eval_w184 product_185

lemma eval_w186 : wordEval w186 = decodeRows r183Rows :=
  wordEval_product eval_w179 eval_w185 product_186

lemma eval_w187 : wordEval w187 = decodeRows r184Rows :=
  wordEval_product eval_w4 eval_w5 product_187

lemma eval_w188 : wordEval w188 = decodeRows r185Rows :=
  wordEval_product eval_y eval_w187 product_188

lemma eval_w189 : wordEval w189 = decodeRows r186Rows :=
  wordEval_product eval_w5 eval_w2 product_189

lemma eval_w190 : wordEval w190 = decodeRows r187Rows :=
  wordEval_product eval_w15 eval_w18 product_190

lemma eval_w191 : wordEval w191 = decodeRows r188Rows :=
  wordEval_product eval_w189 eval_w190 product_191

lemma eval_w192 : wordEval w192 = decodeRows r189Rows :=
  wordEval_product eval_w188 eval_w191 product_192

lemma eval_w193 : wordEval w193 = decodeRows r190Rows :=
  wordEval_product eval_w4 eval_w11 product_193

lemma eval_w194 : wordEval w194 = decodeRows r191Rows :=
  wordEval_product eval_w5 eval_w11 product_194

lemma eval_w195 : wordEval w195 = decodeRows r192Rows :=
  wordEval_product eval_w193 eval_w194 product_195

lemma eval_w196 : wordEval w196 = decodeRows r193Rows :=
  wordEval_product eval_w7 eval_w45 product_196

lemma eval_w197 : wordEval w197 = decodeRows r194Rows :=
  wordEval_product eval_w8 eval_x product_197

lemma eval_w198 : wordEval w198 = decodeRows r195Rows :=
  wordEval_product eval_w196 eval_w197 product_198

lemma eval_w199 : wordEval w199 = decodeRows r196Rows :=
  wordEval_product eval_w195 eval_w198 product_199

lemma eval_w200 : wordEval w200 = decodeRows r197Rows :=
  wordEval_product eval_w192 eval_w199 product_200

lemma eval_w201 : wordEval w201 = decodeRows r198Rows :=
  wordEval_product eval_w0 eval_w10 product_201

lemma eval_w202 : wordEval w202 = decodeRows r199Rows :=
  wordEval_product eval_w46 eval_w37 product_202

lemma eval_w203 : wordEval w203 = decodeRows r200Rows :=
  wordEval_product eval_w23 eval_w202 product_203

lemma eval_w204 : wordEval w204 = decodeRows r201Rows :=
  wordEval_product eval_w201 eval_w203 product_204

lemma eval_w205 : wordEval w205 = decodeRows r202Rows :=
  wordEval_product eval_w57 eval_w3 product_205

lemma eval_w206 : wordEval w206 = decodeRows r203Rows :=
  wordEval_product eval_w49 eval_w205 product_206

lemma eval_w207 : wordEval w207 = decodeRows r204Rows :=
  wordEval_product eval_w32 eval_w1 product_207

lemma eval_w208 : wordEval w208 = decodeRows r205Rows :=
  wordEval_product eval_w45 eval_w207 product_208

lemma eval_w209 : wordEval w209 = decodeRows r206Rows :=
  wordEval_product eval_w206 eval_w208 product_209

lemma eval_w210 : wordEval w210 = decodeRows r207Rows :=
  wordEval_product eval_w204 eval_w209 product_210

lemma eval_w211 : wordEval w211 = decodeRows r208Rows :=
  wordEval_product eval_y eval_w13 product_211

lemma eval_w212 : wordEval w212 = decodeRows r209Rows :=
  wordEval_product eval_w211 eval_w149 product_212

lemma eval_w213 : wordEval w213 = decodeRows r210Rows :=
  wordEval_product eval_w31 eval_w43 product_213

lemma eval_w214 : wordEval w214 = decodeRows r211Rows :=
  wordEval_product eval_w31 eval_x product_214

lemma eval_w215 : wordEval w215 = decodeRows r212Rows :=
  wordEval_product eval_w213 eval_w214 product_215

lemma eval_w216 : wordEval w216 = decodeRows r213Rows :=
  wordEval_product eval_w212 eval_w215 product_216

lemma eval_w217 : wordEval w217 = decodeRows r214Rows :=
  wordEval_product eval_w7 eval_w18 product_217

lemma eval_w218 : wordEval w218 = decodeRows r215Rows :=
  wordEval_product eval_w57 eval_w217 product_218

lemma eval_w219 : wordEval w219 = decodeRows r216Rows :=
  wordEval_product eval_w7 eval_w4 product_219

lemma eval_w220 : wordEval w220 = decodeRows r217Rows :=
  wordEval_product eval_w46 eval_w4 product_220

lemma eval_w221 : wordEval w221 = decodeRows r218Rows :=
  wordEval_product eval_w219 eval_w220 product_221

lemma eval_w222 : wordEval w222 = decodeRows r219Rows :=
  wordEval_product eval_w218 eval_w221 product_222

lemma eval_w223 : wordEval w223 = decodeRows r220Rows :=
  wordEval_product eval_w10 eval_w2 product_223

lemma eval_w224 : wordEval w224 = decodeRows r221Rows :=
  wordEval_product eval_w41 eval_w223 product_224

lemma eval_w225 : wordEval w225 = decodeRows r222Rows :=
  wordEval_product eval_w5 eval_w55 product_225

lemma eval_w226 : wordEval w226 = decodeRows r223Rows :=
  wordEval_product eval_w13 eval_w6 product_226

lemma eval_w227 : wordEval w227 = decodeRows r224Rows :=
  wordEval_product eval_w225 eval_w226 product_227

lemma eval_w228 : wordEval w228 = decodeRows r225Rows :=
  wordEval_product eval_w224 eval_w227 product_228

lemma eval_w229 : wordEval w229 = decodeRows r226Rows :=
  wordEval_product eval_w222 eval_w228 product_229

lemma eval_w230 : wordEval w230 = decodeRows r227Rows :=
  wordEval_product eval_w3 eval_w30 product_230

lemma eval_w231 : wordEval w231 = decodeRows r228Rows :=
  wordEval_product eval_w49 eval_w230 product_231

lemma eval_w232 : wordEval w232 = decodeRows r229Rows :=
  wordEval_product eval_w45 eval_w11 product_232

lemma eval_w233 : wordEval w233 = decodeRows r230Rows :=
  wordEval_product eval_w14 eval_w15 product_233

lemma eval_w234 : wordEval w234 = decodeRows r231Rows :=
  wordEval_product eval_w232 eval_w233 product_234

lemma eval_w235 : wordEval w235 = decodeRows r232Rows :=
  wordEval_product eval_w231 eval_w234 product_235

lemma eval_w236 : wordEval w236 = decodeRows r233Rows :=
  wordEval_product eval_w12 eval_w52 product_236

lemma eval_w237 : wordEval w237 = decodeRows r234Rows :=
  wordEval_product eval_w57 eval_w236 product_237

lemma eval_w238 : wordEval w238 = decodeRows r235Rows :=
  wordEval_product eval_w7 eval_w3 product_238

lemma eval_w239 : wordEval w239 = decodeRows r236Rows :=
  wordEval_product eval_w7 eval_w0 product_239

lemma eval_w240 : wordEval w240 = decodeRows r237Rows :=
  wordEval_product eval_w238 eval_w239 product_240

lemma eval_w241 : wordEval w241 = decodeRows r238Rows :=
  wordEval_product eval_w237 eval_w240 product_241

lemma eval_w242 : wordEval w242 = decodeRows r239Rows :=
  wordEval_product eval_w235 eval_w241 product_242

lemma eval_w243 : wordEval w243 = decodeRows r240Rows :=
  wordEval_product eval_w39 eval_w13 product_243

lemma eval_w244 : wordEval w244 = decodeRows r241Rows :=
  wordEval_product eval_w4 eval_w243 product_244

lemma eval_w245 : wordEval w245 = decodeRows r242Rows :=
  wordEval_product eval_w6 eval_w15 product_245

lemma eval_w246 : wordEval w246 = decodeRows r243Rows :=
  wordEval_product eval_w61 eval_w14 product_246

lemma eval_w247 : wordEval w247 = decodeRows r244Rows :=
  wordEval_product eval_w245 eval_w246 product_247

lemma eval_w248 : wordEval w248 = decodeRows r245Rows :=
  wordEval_product eval_w244 eval_w247 product_248

lemma eval_w249 : wordEval w249 = decodeRows r246Rows :=
  wordEval_product eval_w52 eval_w12 product_249

lemma eval_w250 : wordEval w250 = decodeRows r247Rows :=
  wordEval_product eval_w37 eval_w249 product_250

lemma eval_w251 : wordEval w251 = decodeRows r248Rows :=
  wordEval_product eval_w0 eval_w39 product_251

lemma eval_w252 : wordEval w252 = decodeRows r249Rows :=
  wordEval_product eval_w12 eval_w16 product_252

lemma eval_w253 : wordEval w253 = decodeRows r250Rows :=
  wordEval_product eval_w251 eval_w252 product_253

lemma eval_w254 : wordEval w254 = decodeRows r251Rows :=
  wordEval_product eval_w250 eval_w253 product_254

lemma eval_w255 : wordEval w255 = decodeRows r252Rows :=
  wordEval_product eval_w248 eval_w254 product_255

lemma eval_w256 : wordEval w256 = decodeRows r253Rows :=
  wordEval_product eval_w16 eval_w6 product_256

lemma eval_w257 : wordEval w257 = decodeRows r254Rows :=
  wordEval_product eval_w15 eval_w24 product_257

lemma eval_w258 : wordEval w258 = decodeRows r255Rows :=
  wordEval_product eval_w256 eval_w257 product_258

lemma eval_w259 : wordEval w259 = decodeRows r256Rows :=
  wordEval_product eval_w8 eval_w13 product_259

lemma eval_w260 : wordEval w260 = decodeRows r257Rows :=
  wordEval_product eval_w3 eval_w256 product_260

lemma eval_w261 : wordEval w261 = decodeRows r258Rows :=
  wordEval_product eval_w259 eval_w260 product_261

lemma eval_w262 : wordEval w262 = decodeRows r259Rows :=
  wordEval_product eval_w258 eval_w261 product_262

lemma eval_w263 : wordEval w263 = decodeRows r260Rows :=
  wordEval_product eval_w18 eval_w18 product_263

lemma eval_w264 : wordEval w264 = decodeRows r261Rows :=
  wordEval_product eval_w13 eval_w70 product_264

lemma eval_w265 : wordEval w265 = decodeRows r262Rows :=
  wordEval_product eval_w263 eval_w264 product_265

lemma eval_w266 : wordEval w266 = decodeRows r263Rows :=
  wordEval_product eval_w39 eval_w22 product_266

lemma eval_w267 : wordEval w267 = decodeRows r264Rows :=
  wordEval_product eval_w6 eval_w16 product_267

lemma eval_w268 : wordEval w268 = decodeRows r265Rows :=
  wordEval_product eval_w14 eval_w267 product_268

lemma eval_w269 : wordEval w269 = decodeRows r266Rows :=
  wordEval_product eval_w266 eval_w268 product_269

lemma eval_w270 : wordEval w270 = decodeRows r267Rows :=
  wordEval_product eval_w265 eval_w269 product_270

lemma eval_w271 : wordEval w271 = decodeRows r268Rows :=
  wordEval_product eval_w262 eval_w270 product_271

lemma eval_w272 : wordEval w272 = decodeRows r269Rows :=
  wordEval_product eval_w13 eval_w15 product_272

lemma eval_w273 : wordEval w273 = decodeRows r270Rows :=
  wordEval_product eval_w5 eval_w272 product_273

lemma eval_w274 : wordEval w274 = decodeRows r271Rows :=
  wordEval_product eval_w53 eval_w9 product_274

lemma eval_w275 : wordEval w275 = decodeRows r272Rows :=
  wordEval_product eval_w158 eval_w274 product_275

lemma eval_w276 : wordEval w276 = decodeRows r273Rows :=
  wordEval_product eval_w273 eval_w275 product_276

lemma eval_w277 : wordEval w277 = decodeRows r274Rows :=
  wordEval_product eval_w23 eval_w9 product_277

lemma eval_w278 : wordEval w278 = decodeRows r275Rows :=
  wordEval_product eval_w46 eval_w277 product_278

lemma eval_w279 : wordEval w279 = decodeRows r276Rows :=
  wordEval_product eval_w55 eval_w30 product_279

lemma eval_w280 : wordEval w280 = decodeRows r277Rows :=
  wordEval_product eval_w279 eval_w239 product_280

lemma eval_w281 : wordEval w281 = decodeRows r278Rows :=
  wordEval_product eval_w278 eval_w280 product_281

lemma eval_w282 : wordEval w282 = decodeRows r279Rows :=
  wordEval_product eval_w276 eval_w281 product_282

lemma eval_w283 : wordEval w283 = decodeRows r280Rows :=
  wordEval_product eval_w37 eval_w5 product_283

lemma eval_w284 : wordEval w284 = decodeRows r281Rows :=
  wordEval_product eval_w6 eval_w283 product_284

lemma eval_w285 : wordEval w285 = decodeRows r282Rows :=
  wordEval_product eval_w37 eval_w40 product_285

lemma eval_w286 : wordEval w286 = decodeRows r283Rows :=
  wordEval_product eval_w50 eval_w9 product_286

lemma eval_w287 : wordEval w287 = decodeRows r284Rows :=
  wordEval_product eval_w285 eval_w286 product_287

lemma eval_w288 : wordEval w288 = decodeRows r285Rows :=
  wordEval_product eval_w284 eval_w287 product_288

lemma eval_w289 : wordEval w289 = decodeRows r286Rows :=
  wordEval_product eval_w10 eval_w56 product_289

lemma eval_w290 : wordEval w290 = decodeRows r287Rows :=
  wordEval_product eval_w3 eval_w2 product_290

lemma eval_w291 : wordEval w291 = decodeRows r288Rows :=
  wordEval_product eval_w289 eval_w290 product_291

lemma eval_w292 : wordEval w292 = decodeRows r289Rows :=
  wordEval_product eval_w22 eval_w14 product_292

lemma eval_w293 : wordEval w293 = decodeRows r290Rows :=
  wordEval_product eval_w31 eval_w1 product_293

lemma eval_w294 : wordEval w294 = decodeRows r291Rows :=
  wordEval_product eval_w292 eval_w293 product_294

lemma eval_w295 : wordEval w295 = decodeRows r292Rows :=
  wordEval_product eval_w291 eval_w294 product_295

lemma eval_w296 : wordEval w296 = decodeRows r293Rows :=
  wordEval_product eval_w288 eval_w295 product_296

lemma eval_w297 : wordEval w297 = decodeRows r294Rows :=
  wordEval_product eval_w3 eval_w0 product_297

lemma eval_w298 : wordEval w298 = decodeRows r295Rows :=
  wordEval_product eval_w8 eval_w297 product_298

lemma eval_w299 : wordEval w299 = decodeRows r296Rows :=
  wordEval_product eval_w46 eval_w51 product_299

lemma eval_w300 : wordEval w300 = decodeRows r297Rows :=
  wordEval_product eval_w31 eval_w299 product_300

lemma eval_w301 : wordEval w301 = decodeRows r298Rows :=
  wordEval_product eval_w298 eval_w300 product_301

lemma eval_w302 : wordEval w302 = decodeRows r299Rows :=
  wordEval_product eval_w61 eval_w219 product_302

lemma eval_w303 : wordEval w303 = decodeRows r300Rows :=
  wordEval_product eval_w6 eval_w56 product_303

lemma eval_w304 : wordEval w304 = decodeRows r301Rows :=
  wordEval_product eval_w303 eval_w246 product_304

lemma eval_w305 : wordEval w305 = decodeRows r302Rows :=
  wordEval_product eval_w302 eval_w304 product_305

lemma eval_w306 : wordEval w306 = decodeRows r303Rows :=
  wordEval_product eval_w301 eval_w305 product_306

lemma eval_w307 : wordEval w307 = decodeRows r304Rows :=
  wordEval_product eval_w24 eval_w10 product_307

lemma eval_w308 : wordEval w308 = decodeRows r305Rows :=
  wordEval_product eval_w0 eval_w307 product_308

lemma eval_w309 : wordEval w309 = decodeRows r306Rows :=
  wordEval_product eval_w8 eval_w45 product_309

lemma eval_w310 : wordEval w310 = decodeRows r307Rows :=
  wordEval_product eval_w11 eval_w14 product_310

lemma eval_w311 : wordEval w311 = decodeRows r308Rows :=
  wordEval_product eval_w309 eval_w310 product_311

lemma eval_w312 : wordEval w312 = decodeRows r309Rows :=
  wordEval_product eval_w308 eval_w311 product_312

lemma eval_w313 : wordEval w313 = decodeRows r310Rows :=
  wordEval_product eval_w17 eval_w6 product_313

lemma eval_w314 : wordEval w314 = decodeRows r311Rows :=
  wordEval_product eval_w0 eval_w6 product_314

lemma eval_w315 : wordEval w315 = decodeRows r312Rows :=
  wordEval_product eval_w313 eval_w314 product_315

lemma eval_w316 : wordEval w316 = decodeRows r313Rows :=
  wordEval_product eval_w7 eval_w53 product_316

lemma eval_w317 : wordEval w317 = decodeRows r314Rows :=
  wordEval_product eval_w10 eval_w1 product_317

lemma eval_w318 : wordEval w318 = decodeRows r315Rows :=
  wordEval_product eval_w316 eval_w317 product_318

lemma eval_w319 : wordEval w319 = decodeRows r316Rows :=
  wordEval_product eval_w315 eval_w318 product_319

lemma eval_w320 : wordEval w320 = decodeRows r317Rows :=
  wordEval_product eval_w312 eval_w319 product_320


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
