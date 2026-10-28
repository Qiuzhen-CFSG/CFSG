module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products6
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products7
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Products8

/-!
# Evaluations of the unchanged signed actor words

An inverse is identified by its checked product with the forward matrix.
Concatenation then evaluates every shared subword. Finally the expanded
lists are compared with the actual `actorWords`, including every sign.

Source: ATLAS of Finite Group Representations, R. A. Wilson,
S. J. Nickerson, J. N. Bray, unchanged `J4G1-max2W1` outputs.
See `ActorMatrices/source/README.md` for the inputs and proof boundaries.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Janko4.GeneratorCertificates KernelRows

set_option maxRecDepth 10000

private theorem eval_append {u v : List ℤ} {A B C : Vector ℕ 112}
    (hu : sourceMatrix (sourceWord u) = decodeRows A)
    (hv : sourceMatrix (sourceWord v) = decodeRows B)
    (hp : packedMul A B = C) :
    sourceMatrix (sourceWord (u ++ v)) = decodeRows C := by
  have hh : sourceWord (u ++ v) = sourceWord u * sourceWord v := by
    simp only [sourceWord, List.map_append, List.prod_append]
  rw [hh, map_mul, hu, hv, ← decode_packedMul, hp]

private theorem eval_inverse {a : sourceSubgroup} {A B : Vector ℕ 112}
    (ha : sourceMatrix a = decodeRows A) (h : packedMul A B = packedOne) :
    sourceMatrix a⁻¹ = decodeRows B := by
  have hp : sourceMatrix a * decodeRows B = 1 := by
    rw [ha, ← decode_packedMul, h, decode_packedOne]
  calc
    sourceMatrix a⁻¹ = sourceMatrix a⁻¹ * (sourceMatrix a * decodeRows B) := by
      rw [hp, mul_one]
    _ = decodeRows B := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_x : sourceMatrix (sourceWord [1]) = decodeRows w10Rows := by
  have h : sourceWord [1] = sourceX := by simp [sourceWord, sourceLetter]
  rw [h]
  exact eval_w10

private theorem eval_y : sourceMatrix (sourceWord [2]) = decodeRows w14Rows := by
  have h : sourceWord [2] = sourceY := by simp [sourceWord, sourceLetter]
  rw [h]
  exact eval_w14

private theorem eval_xinv : sourceMatrix (sourceWord [-1]) = decodeRows wordRows1_0 := by
  have h : sourceWord [-1] = sourceX⁻¹ := by simp [sourceWord, sourceLetter]
  rw [h]
  exact eval_inverse eval_w10 product_xinv

private theorem eval_yinv : sourceMatrix (sourceWord [-2]) = decodeRows inverseYRows := by
  have h : sourceWord [-2] = sourceY⁻¹ := by simp [sourceWord, sourceLetter]
  rw [h]
  exact eval_inverse eval_w14 product_yinv

attribute [local irreducible] sourceMatrix sourceWord decodeRows

private theorem eval_part3 : sourceMatrix (sourceWord part3) = decodeRows partRows3 :=
  eval_append eval_xinv eval_yinv product_3

private theorem eval_part4 : sourceMatrix (sourceWord part4) = decodeRows partRows4 :=
  eval_append eval_x eval_yinv product_4

private theorem eval_part5 : sourceMatrix (sourceWord part5) = decodeRows partRows5 :=
  eval_append eval_x eval_y product_5

private theorem eval_part6 : sourceMatrix (sourceWord part6) = decodeRows partRows6 :=
  eval_append eval_xinv eval_y product_6

private theorem eval_part7 : sourceMatrix (sourceWord part7) = decodeRows partRows7 :=
  eval_append eval_part4 eval_part5 product_7

private theorem eval_part8 : sourceMatrix (sourceWord part8) = decodeRows partRows8 :=
  eval_append eval_part3 eval_part3 product_8

private theorem eval_part9 : sourceMatrix (sourceWord part9) = decodeRows partRows9 :=
  eval_append eval_part6 eval_part6 product_9

private theorem eval_part10 : sourceMatrix (sourceWord part10) = decodeRows partRows10 :=
  eval_append eval_part6 eval_part8 product_10

private theorem eval_part11 : sourceMatrix (sourceWord part11) = decodeRows partRows11 :=
  eval_append eval_part4 eval_part7 product_11

private theorem eval_part12 : sourceMatrix (sourceWord part12) = decodeRows partRows12 :=
  eval_append eval_part11 eval_part5 product_12

private theorem eval_part13 : sourceMatrix (sourceWord part13) = decodeRows partRows13 :=
  eval_append eval_part7 eval_part7 product_13

private theorem eval_part14 : sourceMatrix (sourceWord part14) = decodeRows partRows14 :=
  eval_append eval_part10 eval_part9 product_14

private theorem eval_part15 : sourceMatrix (sourceWord part15) = decodeRows partRows15 :=
  eval_append eval_part5 eval_part7 product_15

private theorem eval_part16 : sourceMatrix (sourceWord part16) = decodeRows partRows16 :=
  eval_append eval_part3 eval_part6 product_16

private theorem eval_part17 : sourceMatrix (sourceWord part17) = decodeRows partRows17 :=
  eval_append eval_part4 eval_part12 product_17

private theorem eval_part18 : sourceMatrix (sourceWord part18) = decodeRows partRows18 :=
  eval_append eval_part14 eval_part9 product_18

private theorem eval_part19 : sourceMatrix (sourceWord part19) = decodeRows partRows19 :=
  eval_append eval_part12 eval_part13 product_19

private theorem eval_part20 : sourceMatrix (sourceWord part20) = decodeRows partRows20 :=
  eval_append eval_part17 eval_part8 product_20

private theorem eval_part21 : sourceMatrix (sourceWord part21) = decodeRows partRows21 :=
  eval_append eval_part10 eval_part10 product_21

private theorem eval_part22 : sourceMatrix (sourceWord part22) = decodeRows partRows22 :=
  eval_append eval_part13 eval_part19 product_22

private theorem eval_part23 : sourceMatrix (sourceWord part23) = decodeRows partRows23 :=
  eval_append eval_part22 eval_part20 product_23

private theorem eval_part24 : sourceMatrix (sourceWord part24) = decodeRows partRows24 :=
  eval_append eval_part23 eval_part9 product_24

private theorem eval_part25 : sourceMatrix (sourceWord part25) = decodeRows partRows25 :=
  eval_append eval_part12 eval_part5 product_25

private theorem eval_part26 : sourceMatrix (sourceWord part26) = decodeRows partRows26 :=
  eval_append eval_part4 eval_part4 product_26

private theorem eval_part27 : sourceMatrix (sourceWord part27) = decodeRows partRows27 :=
  eval_append eval_part14 eval_part18 product_27

private theorem eval_part28 : sourceMatrix (sourceWord part28) = decodeRows partRows28 :=
  eval_append eval_part27 eval_part21 product_28

private theorem eval_part29 : sourceMatrix (sourceWord part29) = decodeRows partRows29 :=
  eval_append eval_part24 eval_part3 product_29

private theorem eval_part30 : sourceMatrix (sourceWord part30) = decodeRows partRows30 :=
  eval_append eval_part16 eval_part16 product_30

private theorem eval_part31 : sourceMatrix (sourceWord part31) = decodeRows partRows31 :=
  eval_append eval_part3 eval_part10 product_31

private theorem eval_part32 : sourceMatrix (sourceWord part32) = decodeRows partRows32 :=
  eval_append eval_part8 eval_part3 product_32

private theorem eval_part33 : sourceMatrix (sourceWord part33) = decodeRows partRows33 :=
  eval_append eval_part5 eval_part15 product_33

private theorem eval_part34 : sourceMatrix (sourceWord part34) = decodeRows partRows34 :=
  eval_append eval_part18 eval_part8 product_34

private theorem eval_part35 : sourceMatrix (sourceWord part35) = decodeRows partRows35 :=
  eval_append eval_part28 eval_part8 product_35

private theorem eval_part36 : sourceMatrix (sourceWord part36) = decodeRows partRows36 :=
  eval_append eval_part15 eval_part11 product_36

private theorem eval_part37 : sourceMatrix (sourceWord part37) = decodeRows partRows37 :=
  eval_append eval_part6 eval_part16 product_37

private theorem eval_part38 : sourceMatrix (sourceWord part38) = decodeRows partRows38 :=
  eval_append eval_y eval_part5 product_38

private theorem eval_part39 : sourceMatrix (sourceWord part39) = decodeRows partRows39 :=
  eval_append eval_part3 eval_part14 product_39

private theorem eval_part40 : sourceMatrix (sourceWord part40) = decodeRows partRows40 :=
  eval_append eval_yinv eval_part8 product_40

private theorem eval_part41 : sourceMatrix (sourceWord part41) = decodeRows partRows41 :=
  eval_append eval_part3 eval_xinv product_41

private theorem eval_part42 : sourceMatrix (sourceWord part42) = decodeRows partRows42 :=
  eval_append eval_part28 eval_yinv product_42

private theorem eval_part43 : sourceMatrix (sourceWord part43) = decodeRows partRows43 :=
  eval_append eval_part29 eval_part5 product_43

private theorem eval_part44 : sourceMatrix (sourceWord part44) = decodeRows partRows44 :=
  eval_append eval_part34 eval_part32 product_44

private theorem eval_part45 : sourceMatrix (sourceWord part45) = decodeRows partRows45 :=
  eval_append eval_part15 eval_part4 product_45

private theorem eval_part46 : sourceMatrix (sourceWord part46) = decodeRows partRows46 :=
  eval_append eval_part11 eval_part26 product_46

private theorem eval_part47 : sourceMatrix (sourceWord part47) = decodeRows partRows47 :=
  eval_append eval_part9 eval_part8 product_47

private theorem eval_part48 : sourceMatrix (sourceWord part48) = decodeRows partRows48 :=
  eval_append eval_part35 eval_part29 product_48

private theorem eval_part49 : sourceMatrix (sourceWord part49) = decodeRows partRows49 :=
  eval_append eval_part36 eval_part20 product_49

private theorem eval_part50 : sourceMatrix (sourceWord part50) = decodeRows partRows50 :=
  eval_append eval_part48 eval_part49 product_50

private theorem eval_part51 : sourceMatrix (sourceWord part51) = decodeRows partRows51 :=
  eval_append eval_part37 eval_part38 product_51

private theorem eval_part52 : sourceMatrix (sourceWord part52) = decodeRows partRows52 :=
  eval_append eval_part13 eval_part15 product_52

private theorem eval_part53 : sourceMatrix (sourceWord part53) = decodeRows partRows53 :=
  eval_append eval_part51 eval_part52 product_53

private theorem eval_part54 : sourceMatrix (sourceWord part54) = decodeRows wordRows1_2 :=
  eval_append eval_part50 eval_part53 product_54

private theorem eval_part55 : sourceMatrix (sourceWord part55) = decodeRows partRows55 :=
  eval_append eval_y eval_part31 product_55

private theorem eval_part56 : sourceMatrix (sourceWord part56) = decodeRows partRows56 :=
  eval_append eval_part32 eval_part9 product_56

private theorem eval_part57 : sourceMatrix (sourceWord part57) = decodeRows partRows57 :=
  eval_append eval_part55 eval_part56 product_57

private theorem eval_part58 : sourceMatrix (sourceWord part58) = decodeRows partRows58 :=
  eval_append eval_part16 eval_part13 product_58

private theorem eval_part59 : sourceMatrix (sourceWord part59) = decodeRows partRows59 :=
  eval_append eval_part36 eval_part39 product_59

private theorem eval_part60 : sourceMatrix (sourceWord part60) = decodeRows partRows60 :=
  eval_append eval_part58 eval_part59 product_60

private theorem eval_part61 : sourceMatrix (sourceWord part61) = decodeRows partRows61 :=
  eval_append eval_part57 eval_part60 product_61

private theorem eval_part62 : sourceMatrix (sourceWord part62) = decodeRows partRows62 :=
  eval_append eval_part8 eval_part12 product_62

private theorem eval_part63 : sourceMatrix (sourceWord part63) = decodeRows partRows63 :=
  eval_append eval_part4 eval_part3 product_63

private theorem eval_part64 : sourceMatrix (sourceWord part64) = decodeRows partRows64 :=
  eval_append eval_part62 eval_part63 product_64

private theorem eval_part65 : sourceMatrix (sourceWord part65) = decodeRows partRows65 :=
  eval_append eval_part9 eval_part37 product_65

private theorem eval_part66 : sourceMatrix (sourceWord part66) = decodeRows partRows66 :=
  eval_append eval_part30 eval_xinv product_66

private theorem eval_part67 : sourceMatrix (sourceWord part67) = decodeRows partRows67 :=
  eval_append eval_part39 eval_part66 product_67

private theorem eval_part68 : sourceMatrix (sourceWord part68) = decodeRows partRows68 :=
  eval_append eval_part65 eval_part67 product_68

private theorem eval_part69 : sourceMatrix (sourceWord part69) = decodeRows partRows69 :=
  eval_append eval_part64 eval_part68 product_69

private theorem eval_part70 : sourceMatrix (sourceWord part70) = decodeRows wordRows1_3 :=
  eval_append eval_part61 eval_part69 product_70

private theorem eval_part71 : sourceMatrix (sourceWord part71) = decodeRows partRows71 :=
  eval_append eval_part40 eval_part9 product_71

private theorem eval_part72 : sourceMatrix (sourceWord part72) = decodeRows partRows72 :=
  eval_append eval_part31 eval_part41 product_72

private theorem eval_part73 : sourceMatrix (sourceWord part73) = decodeRows partRows73 :=
  eval_append eval_xinv eval_part72 product_73

private theorem eval_part74 : sourceMatrix (sourceWord part74) = decodeRows wordRows2_0 :=
  eval_append eval_part71 eval_part73 product_74

private theorem eval_part75 : sourceMatrix (sourceWord part75) = decodeRows partRows75 :=
  eval_append eval_y eval_part13 product_75

private theorem eval_part76 : sourceMatrix (sourceWord part76) = decodeRows partRows76 :=
  eval_append eval_part7 eval_part33 product_76

private theorem eval_part77 : sourceMatrix (sourceWord part77) = decodeRows partRows77 :=
  eval_append eval_part75 eval_part76 product_77

private theorem eval_part78 : sourceMatrix (sourceWord part78) = decodeRows partRows78 :=
  eval_append eval_part33 eval_y product_78

private theorem eval_part79 : sourceMatrix (sourceWord part79) = decodeRows partRows79 :=
  eval_append eval_part10 eval_xinv product_79

private theorem eval_part80 : sourceMatrix (sourceWord part80) = decodeRows partRows80 :=
  eval_append eval_part9 eval_part79 product_80

private theorem eval_part81 : sourceMatrix (sourceWord part81) = decodeRows partRows81 :=
  eval_append eval_part78 eval_part80 product_81

private theorem eval_part82 : sourceMatrix (sourceWord part82) = decodeRows wordRows2_1 :=
  eval_append eval_part77 eval_part81 product_82

private theorem eval_part83 : sourceMatrix (sourceWord part83) = decodeRows partRows83 :=
  eval_append eval_part4 eval_part10 product_83

private theorem eval_part84 : sourceMatrix (sourceWord part84) = decodeRows partRows84 :=
  eval_append eval_part42 eval_part83 product_84

private theorem eval_part85 : sourceMatrix (sourceWord part85) = decodeRows partRows85 :=
  eval_append eval_part30 eval_part3 product_85

private theorem eval_part86 : sourceMatrix (sourceWord part86) = decodeRows partRows86 :=
  eval_append eval_part34 eval_xinv product_86

private theorem eval_part87 : sourceMatrix (sourceWord part87) = decodeRows partRows87 :=
  eval_append eval_part85 eval_part86 product_87

private theorem eval_part88 : sourceMatrix (sourceWord part88) = decodeRows wordRows2_2 :=
  eval_append eval_part84 eval_part87 product_88

private theorem eval_part89 : sourceMatrix (sourceWord part89) = decodeRows partRows89 :=
  eval_append eval_part11 eval_part25 product_89

private theorem eval_part90 : sourceMatrix (sourceWord part90) = decodeRows partRows90 :=
  eval_append eval_part43 eval_part89 product_90

private theorem eval_part91 : sourceMatrix (sourceWord part91) = decodeRows partRows91 :=
  eval_append eval_part13 eval_part17 product_91

private theorem eval_part92 : sourceMatrix (sourceWord part92) = decodeRows partRows92 :=
  eval_append eval_part44 eval_yinv product_92

private theorem eval_part93 : sourceMatrix (sourceWord part93) = decodeRows partRows93 :=
  eval_append eval_part91 eval_part92 product_93

private theorem eval_part94 : sourceMatrix (sourceWord part94) = decodeRows wordRows2_3 :=
  eval_append eval_part90 eval_part93 product_94

private theorem eval_part95 : sourceMatrix (sourceWord part95) = decodeRows partRows95 :=
  eval_append eval_part35 eval_part24 product_95

private theorem eval_part96 : sourceMatrix (sourceWord part96) = decodeRows partRows96 :=
  eval_append eval_part5 eval_part19 product_96

private theorem eval_part97 : sourceMatrix (sourceWord part97) = decodeRows partRows97 :=
  eval_append eval_part6 eval_part96 product_97

private theorem eval_part98 : sourceMatrix (sourceWord part98) = decodeRows partRows98 :=
  eval_append eval_part95 eval_part97 product_98

private theorem eval_part99 : sourceMatrix (sourceWord part99) = decodeRows partRows99 :=
  eval_append eval_part15 eval_part25 product_99

private theorem eval_part100 : sourceMatrix (sourceWord part100) = decodeRows partRows100 :=
  eval_append eval_part25 eval_x product_100

private theorem eval_part101 : sourceMatrix (sourceWord part101) = decodeRows partRows101 :=
  eval_append eval_part5 eval_part100 product_101

private theorem eval_part102 : sourceMatrix (sourceWord part102) = decodeRows partRows102 :=
  eval_append eval_part99 eval_part101 product_102

private theorem eval_part103 : sourceMatrix (sourceWord part103) = decodeRows wordRows3_0 :=
  eval_append eval_part98 eval_part102 product_103

private theorem eval_part104 : sourceMatrix (sourceWord part104) = decodeRows partRows104 :=
  eval_append eval_part45 eval_part46 product_104

private theorem eval_part105 : sourceMatrix (sourceWord part105) = decodeRows partRows105 :=
  eval_append eval_part42 eval_part104 product_105

private theorem eval_part106 : sourceMatrix (sourceWord part106) = decodeRows partRows106 :=
  eval_append eval_part47 eval_part8 product_106

private theorem eval_part107 : sourceMatrix (sourceWord part107) = decodeRows partRows107 :=
  eval_append eval_xinv eval_part44 product_107

private theorem eval_part108 : sourceMatrix (sourceWord part108) = decodeRows partRows108 :=
  eval_append eval_part106 eval_part107 product_108

private theorem eval_part109 : sourceMatrix (sourceWord part109) = decodeRows wordRows3_1 :=
  eval_append eval_part105 eval_part108 product_109

private theorem eval_part110 : sourceMatrix (sourceWord part110) = decodeRows partRows110 :=
  eval_append eval_part43 eval_part5 product_110

private theorem eval_part111 : sourceMatrix (sourceWord part111) = decodeRows partRows111 :=
  eval_append eval_part33 eval_part47 product_111

private theorem eval_part112 : sourceMatrix (sourceWord part112) = decodeRows partRows112 :=
  eval_append eval_part110 eval_part111 product_112

private theorem eval_part113 : sourceMatrix (sourceWord part113) = decodeRows partRows113 :=
  eval_append eval_part21 eval_yinv product_113

private theorem eval_part114 : sourceMatrix (sourceWord part114) = decodeRows partRows114 :=
  eval_append eval_part5 eval_part11 product_114

private theorem eval_part115 : sourceMatrix (sourceWord part115) = decodeRows partRows115 :=
  eval_append eval_part15 eval_part114 product_115

private theorem eval_part116 : sourceMatrix (sourceWord part116) = decodeRows partRows116 :=
  eval_append eval_part113 eval_part115 product_116

private theorem eval_part117 : sourceMatrix (sourceWord part117) = decodeRows wordRows3_2 :=
  eval_append eval_part112 eval_part116 product_117

private theorem eval_part118 : sourceMatrix (sourceWord part118) = decodeRows partRows118 :=
  eval_append eval_part40 eval_part10 product_118

private theorem eval_part119 : sourceMatrix (sourceWord part119) = decodeRows partRows119 :=
  eval_append eval_part31 eval_part30 product_119

private theorem eval_part120 : sourceMatrix (sourceWord part120) = decodeRows partRows120 :=
  eval_append eval_part118 eval_part119 product_120

private theorem eval_part121 : sourceMatrix (sourceWord part121) = decodeRows partRows121 :=
  eval_append eval_part16 eval_part38 product_121

private theorem eval_part122 : sourceMatrix (sourceWord part122) = decodeRows partRows122 :=
  eval_append eval_part46 eval_part4 product_122

private theorem eval_part123 : sourceMatrix (sourceWord part123) = decodeRows partRows123 :=
  eval_append eval_part26 eval_part122 product_123

private theorem eval_part124 : sourceMatrix (sourceWord part124) = decodeRows partRows124 :=
  eval_append eval_part121 eval_part123 product_124

private theorem eval_part125 : sourceMatrix (sourceWord part125) = decodeRows wordRows3_3 :=
  eval_append eval_part120 eval_part124 product_125

private theorem eval_part126 : sourceMatrix (sourceWord part126) = decodeRows partRows126 :=
  eval_append eval_part29 eval_part25 product_126

private theorem eval_part127 : sourceMatrix (sourceWord part127) = decodeRows partRows127 :=
  eval_append eval_part25 eval_part12 product_127

private theorem eval_part128 : sourceMatrix (sourceWord part128) = decodeRows partRows128 :=
  eval_append eval_part126 eval_part127 product_128

private theorem eval_part129 : sourceMatrix (sourceWord part129) = decodeRows partRows129 :=
  eval_append eval_x eval_part45 product_129

private theorem eval_part130 : sourceMatrix (sourceWord part130) = decodeRows partRows130 :=
  eval_append eval_part26 eval_part41 product_130

private theorem eval_part131 : sourceMatrix (sourceWord part131) = decodeRows partRows131 :=
  eval_append eval_part17 eval_part130 product_131

private theorem eval_part132 : sourceMatrix (sourceWord part132) = decodeRows partRows132 :=
  eval_append eval_part129 eval_part131 product_132

private theorem eval_part133 : sourceMatrix (sourceWord part133) = decodeRows wordRows3_4 :=
  eval_append eval_part128 eval_part132 product_133

theorem eval_words1 :
    ((actorWords 1).map sourceWord).map sourceMatrix =
      (wordRows 1).map decodeRows := by
  have hw : actorWords 1 = [([-1] : List ℤ), ([-1] : List ℤ), part54, part70] := by
    decide +kernel
  rw [hw]
  simp only [List.map_cons, List.map_nil]
  rw [eval_xinv, eval_part54, eval_part70]
  rfl

theorem eval_words2 :
    ((actorWords 2).map sourceWord).map sourceMatrix =
      (wordRows 2).map decodeRows := by
  have hw : actorWords 2 = [part74, part82, part88, part94] := by
    decide +kernel
  rw [hw]
  simp only [List.map_cons, List.map_nil]
  rw [eval_part74, eval_part82, eval_part88, eval_part94]
  rfl

theorem eval_words3 :
    ((actorWords 3).map sourceWord).map sourceMatrix =
      (wordRows 3).map decodeRows := by
  have hw : actorWords 3 = [part103, part109, part117, part125, part133] := by
    decide +kernel
  rw [hw]
  simp only [List.map_cons, List.map_nil]
  rw [eval_part103, eval_part109, eval_part117, eval_part125, eval_part133]
  rfl

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
