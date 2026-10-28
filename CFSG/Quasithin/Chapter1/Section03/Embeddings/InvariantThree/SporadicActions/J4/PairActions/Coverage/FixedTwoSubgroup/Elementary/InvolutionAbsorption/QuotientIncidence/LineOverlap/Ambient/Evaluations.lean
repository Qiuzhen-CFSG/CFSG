module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products000
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products001
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products002
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products003
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products004
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products005
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products006
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products007
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products008
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products009
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products010
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products011
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products012
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products013
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products014
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products015
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products016
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products017
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products018
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products019
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products020
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Products021
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Evaluations

/-!
# Actual max4 outputs and the ambient conjugator

The explicit words are evaluated using certified matrix products. The first
two words are definitionally the outputs of the literal ATLAS max4 program.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates

open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] Janko4.modelGroup

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData

def v0 : Model := Janko4.a * Janko4.b

def v1 : Model := v0 ^ 2

def v2 : Model := v0 ^ 3

def v3 : Model := v2 * Janko4.b

def v4 : Model := Janko4.b * Janko4.a

def v5 : Model := v3 * Janko4.b

def v6 : Model := v5 ^ 2

def v7 : Model := v5 ^ 3

def v8 : Model := v4 ^ 2

def v9 : Model := v4 ^ 3

def v10 : Model := v4 ^ 5

def v11 : Model := v4 ^ 6

def v12 : Model := v4 ^ 11

def v13 : Model := v4 ^ 22

def v14 : Model := v0 ^ 2

def v15 : Model := v0 ^ 3

def v16 : Model := v0 ^ 6

def v17 : Model := v0 ^ 4

def v18 : Model := v0 ^ 7

def v19 : Model := v0 ^ 13

def v20 : Model := v13 * v19

def v21 : Model := v4 * v4

def v22 : Model := v20⁻¹

def v23 : Model := v22 * v7

def v24 : Model := v7 * v7

def v25 : Model := v23 * v20

def v26 : Model := v21⁻¹

def v27 : Model := v26 * v24

def v28 : Model := v27 * v21

def max4U : Model := (max4Program Janko4.a Janko4.b).1

def max4V : Model := (max4Program Janko4.a Janko4.b).2

def v31 : Model := v28⁻¹

def v32 : Model := v25⁻¹

def v33 : Model := v25 * v28

def v34 : Model := v33 * v25

def v35 : Model := v34 * v31

def v36 : Model := v35 * v31

def v37 : Model := v36 * v28

def v38 : Model := v37 * v31

def v39 : Model := v38 * v31

def v40 : Model := v39 * v28

def v41 : Model := v40 * v31

def v42 : Model := v41 * v32

def v43 : Model := v42 * v28

def v44 : Model := v43 ^ 2

def v45 : Model := v43 ^ 3

def v46 : Model := v43 ^ 6

def v47 : Model := v43 ^ 4

def v48 : Model := v43 ^ 7

def v49 : Model := v43 ^ 13

def v50 : Model := v43 ^ 26

def v51 : Model := v43 ^ 52

def v52 : Model := v43 ^ 14

def v53 : Model := v43 ^ 27

def v54 : Model := v43 ^ 53

def v55 : Model := v43 ^ 105

def v56 : Model := v43 ^ 210

def v57 : Model := Janko4.b * Janko4.b

def v58 : Model := v57 * Janko4.a

def v59 : Model := Janko4.b⁻¹

def v60 : Model := v58 * v59

def v61 : Model := v60 * Janko4.a

def v62 : Model := v61 * Janko4.b

def v63 : Model := v62⁻¹

def v64 : Model := v63 * v56

def v65 : Model := v64 * v62

def v66 : Model := v65 * TwoCoreCentralizerData.t

def v67 : Model := v66 ^ 2

def v68 : Model := v66 ^ 3

def v69 : Model := v66 ^ 6

def v70 : Model := v62 * v69

def v71 : Model := w14⁻¹

def v72 : Model := v71 * w10

def v73 : Model := w14⁻¹

def v74 : Model := v72 * v73

def v75 : Model := v74 * w10

def v76 : Model := v75 * w14

def v77 : Model := v76 * w10

def v78 : Model := v77 * w14

def v79 : Model := v78 * w10

def v80 : Model := v79 * w14

def v81 : Model := v70 * v80

def rightConjugator : Model := v81

def v83 : Model := w14⁻¹

def v84 : Model := w10 * v83

def v85 : Model := v84 * w10

def v86 : Model := v85 * w14

def v87 : Model := v86 * w10

def v88 : Model := v87 * w14

def v89 : Model := v88 * w10

def v90 : Model := v89 * w14

def v91 : Model := v90 * w10

def v92 : Model := v91 * v83

def v93 : Model := v92 * w10

def v94 : Model := v93 * w14

def v95 : Model := v94 * w10

def v96 : Model := v95 * v83

def v97 : Model := w10 * v83

def v98 : Model := v97 * w10

def v99 : Model := v98 * w14

def v100 : Model := v99 * w10

def v101 : Model := v100 * v83

def v102 : Model := v101 * w10

def v103 : Model := v102 * v83

def v104 : Model := v103 * w10

def v105 : Model := v104 * w14

def v106 : Model := v105 * w10

def v107 : Model := v106 * v83

def v108 : Model := v107 * w10

def v109 : Model := v108 * v83

def v110 : Model := v109 * w10

def v111 : Model := v110 * v83

def v112 : Model := v111 * w10

def v113 : Model := v112 * w14

def v114 : Model := v113 * w10

def v115 : Model := v114 * v83

theorem eval_v0 : toMatrix v0 = decodeRows r0 :=
  eval_mul (by rfl) (by rfl) product_0

theorem eval_v1 : toMatrix v1 = decodeRows r1 :=
  eval_pow_add (g := v0) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v0) (by simpa only [pow_one] using eval_v0) product_1

theorem eval_v2 : toMatrix v2 = decodeRows r2 :=
  eval_pow_add (g := v0) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v0) eval_v1 product_2

theorem eval_v3 : toMatrix v3 = decodeRows r3 :=
  eval_mul eval_v2 (by rfl) product_3

theorem eval_v4 : toMatrix v4 = decodeRows r4 :=
  eval_mul (by rfl) (by rfl) product_4

theorem eval_v5 : toMatrix v5 = decodeRows r5 :=
  eval_mul eval_v3 (by rfl) product_5

theorem eval_v6 : toMatrix v6 = decodeRows r6 :=
  eval_pow_add (g := v5) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v5) (by simpa only [pow_one] using eval_v5) product_6

theorem eval_v7 : toMatrix v7 = decodeRows r7 :=
  eval_pow_add (g := v5) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v5) eval_v6 product_7

theorem eval_v8 : toMatrix v8 = decodeRows r8 :=
  eval_pow_add (g := v4) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v4) (by simpa only [pow_one] using eval_v4) product_8

theorem eval_v9 : toMatrix v9 = decodeRows r9 :=
  eval_pow_add (g := v4) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v4) eval_v8 product_9

theorem eval_v10 : toMatrix v10 = decodeRows r10 :=
  eval_pow_add (g := v4) (m := 2) (n := 3) eval_v8 eval_v9 product_10

theorem eval_v11 : toMatrix v11 = decodeRows r11 :=
  eval_pow_add (g := v4) (m := 3) (n := 3) eval_v9 eval_v9 product_11

theorem eval_v12 : toMatrix v12 = decodeRows r12 :=
  eval_pow_add (g := v4) (m := 5) (n := 6) eval_v10 eval_v11 product_12

theorem eval_v13 : toMatrix v13 = decodeRows r13 :=
  eval_pow_add (g := v4) (m := 11) (n := 11) eval_v12 eval_v12 product_13

theorem eval_v14 : toMatrix v14 = decodeRows r1 :=
  eval_pow_add (g := v0) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v0) (by simpa only [pow_one] using eval_v0) product_1

theorem eval_v15 : toMatrix v15 = decodeRows r2 :=
  eval_pow_add (g := v0) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v0) eval_v14 product_2

theorem eval_v16 : toMatrix v16 = decodeRows r14 :=
  eval_pow_add (g := v0) (m := 3) (n := 3) eval_v15 eval_v15 product_14

theorem eval_v17 : toMatrix v17 = decodeRows r15 :=
  eval_pow_add (g := v0) (m := 2) (n := 2) eval_v14 eval_v14 product_15

theorem eval_v18 : toMatrix v18 = decodeRows r16 :=
  eval_pow_add (g := v0) (m := 3) (n := 4) eval_v15 eval_v17 product_16

theorem eval_v19 : toMatrix v19 = decodeRows r17 :=
  eval_pow_add (g := v0) (m := 6) (n := 7) eval_v16 eval_v18 product_17

theorem eval_v20 : toMatrix v20 = decodeRows r18 :=
  eval_mul eval_v13 eval_v19 product_18

theorem eval_v21 : toMatrix v21 = decodeRows r8 :=
  eval_mul eval_v4 eval_v4 product_8

theorem eval_v22 : toMatrix v22 = decodeRows r19 :=
  eval_inv eval_v20 product_19

theorem eval_v23 : toMatrix v23 = decodeRows r20 :=
  eval_mul eval_v22 eval_v7 product_20

theorem eval_v24 : toMatrix v24 = decodeRows r21 :=
  eval_mul eval_v7 eval_v7 product_21

theorem eval_v25 : toMatrix v25 = decodeRows r22 :=
  eval_mul eval_v23 eval_v20 product_22

theorem eval_v26 : toMatrix v26 = decodeRows r23 :=
  eval_inv eval_v21 product_23

theorem eval_v27 : toMatrix v27 = decodeRows r24 :=
  eval_mul eval_v26 eval_v24 product_24

theorem eval_v28 : toMatrix v28 = decodeRows r25 :=
  eval_mul eval_v27 eval_v21 product_25

theorem eval_max4U : toMatrix max4U = decodeRows r25 := eval_v28

theorem eval_max4V : toMatrix max4V = decodeRows r22 := eval_v25

theorem eval_v31 : toMatrix v31 = decodeRows r25 :=
  eval_inv eval_v28 product_26

theorem eval_v32 : toMatrix v32 = decodeRows r26 :=
  eval_inv eval_v25 product_27

theorem eval_v33 : toMatrix v33 = decodeRows r27 :=
  eval_mul eval_v25 eval_v28 product_28

theorem eval_v34 : toMatrix v34 = decodeRows r28 :=
  eval_mul eval_v33 eval_v25 product_29

theorem eval_v35 : toMatrix v35 = decodeRows r29 :=
  eval_mul eval_v34 eval_v31 product_30

theorem eval_v36 : toMatrix v36 = decodeRows r28 :=
  eval_mul eval_v35 eval_v31 product_31

theorem eval_v37 : toMatrix v37 = decodeRows r29 :=
  eval_mul eval_v36 eval_v28 product_30

theorem eval_v38 : toMatrix v38 = decodeRows r28 :=
  eval_mul eval_v37 eval_v31 product_31

theorem eval_v39 : toMatrix v39 = decodeRows r29 :=
  eval_mul eval_v38 eval_v31 product_30

theorem eval_v40 : toMatrix v40 = decodeRows r28 :=
  eval_mul eval_v39 eval_v28 product_31

theorem eval_v41 : toMatrix v41 = decodeRows r29 :=
  eval_mul eval_v40 eval_v31 product_30

theorem eval_v42 : toMatrix v42 = decodeRows r30 :=
  eval_mul eval_v41 eval_v32 product_32

theorem eval_v43 : toMatrix v43 = decodeRows r31 :=
  eval_mul eval_v42 eval_v28 product_33

theorem eval_v44 : toMatrix v44 = decodeRows r32 :=
  eval_pow_add (g := v43) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v43) (by simpa only [pow_one] using eval_v43) product_34

theorem eval_v45 : toMatrix v45 = decodeRows r33 :=
  eval_pow_add (g := v43) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v43) eval_v44 product_35

theorem eval_v46 : toMatrix v46 = decodeRows r34 :=
  eval_pow_add (g := v43) (m := 3) (n := 3) eval_v45 eval_v45 product_36

theorem eval_v47 : toMatrix v47 = decodeRows r35 :=
  eval_pow_add (g := v43) (m := 2) (n := 2) eval_v44 eval_v44 product_37

theorem eval_v48 : toMatrix v48 = decodeRows r36 :=
  eval_pow_add (g := v43) (m := 3) (n := 4) eval_v45 eval_v47 product_38

theorem eval_v49 : toMatrix v49 = decodeRows r31 :=
  eval_pow_add (g := v43) (m := 6) (n := 7) eval_v46 eval_v48 product_39

theorem eval_v50 : toMatrix v50 = decodeRows r32 :=
  eval_pow_add (g := v43) (m := 13) (n := 13) eval_v49 eval_v49 product_34

theorem eval_v51 : toMatrix v51 = decodeRows r35 :=
  eval_pow_add (g := v43) (m := 26) (n := 26) eval_v50 eval_v50 product_37

theorem eval_v52 : toMatrix v52 = decodeRows r32 :=
  eval_pow_add (g := v43) (m := 7) (n := 7) eval_v48 eval_v48 product_40

theorem eval_v53 : toMatrix v53 = decodeRows r33 :=
  eval_pow_add (g := v43) (m := 13) (n := 14) eval_v49 eval_v52 product_35

theorem eval_v54 : toMatrix v54 = decodeRows r37 :=
  eval_pow_add (g := v43) (m := 26) (n := 27) eval_v50 eval_v53 product_41

theorem eval_v55 : toMatrix v55 = decodeRows r38 :=
  eval_pow_add (g := v43) (m := 52) (n := 53) eval_v51 eval_v54 product_42

theorem eval_v56 : toMatrix v56 = decodeRows r34 :=
  eval_pow_add (g := v43) (m := 105) (n := 105) eval_v55 eval_v55 product_43

theorem eval_v57 : toMatrix v57 = decodeRows r39 :=
  eval_mul (by rfl) (by rfl) product_44

theorem eval_v58 : toMatrix v58 = decodeRows r40 :=
  eval_mul eval_v57 (by rfl) product_45

theorem eval_v59 : toMatrix v59 = decodeRows r41 :=
  eval_inv (by rfl) product_46

theorem eval_v60 : toMatrix v60 = decodeRows r42 :=
  eval_mul eval_v58 eval_v59 product_47

theorem eval_v61 : toMatrix v61 = decodeRows r43 :=
  eval_mul eval_v60 (by rfl) product_48

theorem eval_v62 : toMatrix v62 = decodeRows r44 :=
  eval_mul eval_v61 (by rfl) product_49

theorem eval_v63 : toMatrix v63 = decodeRows r45 :=
  eval_inv eval_v62 product_50

theorem eval_v64 : toMatrix v64 = decodeRows r46 :=
  eval_mul eval_v63 eval_v56 product_51

theorem eval_v65 : toMatrix v65 = decodeRows r47 :=
  eval_mul eval_v64 eval_v62 product_52

theorem eval_v66 : toMatrix v66 = decodeRows r48 :=
  eval_mul eval_v65 TwoCoreCentralizerData.eval_t product_53

theorem eval_v67 : toMatrix v67 = decodeRows r50 :=
  eval_pow_add (g := v66) (m := 1) (n := 1) (by simpa only [pow_one] using eval_v66) (by simpa only [pow_one] using eval_v66) product_54

theorem eval_v68 : toMatrix v68 = decodeRows r51 :=
  eval_pow_add (g := v66) (m := 1) (n := 2) (by simpa only [pow_one] using eval_v66) eval_v67 product_55

theorem eval_v69 : toMatrix v69 = decodeRows r52 :=
  eval_pow_add (g := v66) (m := 3) (n := 3) eval_v68 eval_v68 product_56

theorem eval_v70 : toMatrix v70 = decodeRows r53 :=
  eval_mul eval_v62 eval_v69 product_57

theorem eval_v71 : toMatrix v71 = decodeRows r54 :=
  eval_inv TwoCoreCentralizerData.eval_w14 product_58

theorem eval_v72 : toMatrix v72 = decodeRows r56 :=
  eval_mul eval_v71 TwoCoreCentralizerData.eval_w10 product_59

theorem eval_v73 : toMatrix v73 = decodeRows r54 :=
  eval_inv TwoCoreCentralizerData.eval_w14 product_58

theorem eval_v74 : toMatrix v74 = decodeRows r58 :=
  eval_mul eval_v72 eval_v73 product_60

theorem eval_v75 : toMatrix v75 = decodeRows r59 :=
  eval_mul eval_v74 TwoCoreCentralizerData.eval_w10 product_61

theorem eval_v76 : toMatrix v76 = decodeRows r60 :=
  eval_mul eval_v75 TwoCoreCentralizerData.eval_w14 product_62

theorem eval_v77 : toMatrix v77 = decodeRows r61 :=
  eval_mul eval_v76 TwoCoreCentralizerData.eval_w10 product_63

theorem eval_v78 : toMatrix v78 = decodeRows r62 :=
  eval_mul eval_v77 TwoCoreCentralizerData.eval_w14 product_64

theorem eval_v79 : toMatrix v79 = decodeRows r63 :=
  eval_mul eval_v78 TwoCoreCentralizerData.eval_w10 product_65

theorem eval_v80 : toMatrix v80 = decodeRows r64 :=
  eval_mul eval_v79 TwoCoreCentralizerData.eval_w14 product_66

theorem eval_v81 : toMatrix v81 = decodeRows r65 :=
  eval_mul eval_v70 eval_v80 product_67

theorem eval_rightConjugator : toMatrix rightConjugator = decodeRows r65 := eval_v81

theorem eval_v83 : toMatrix v83 = decodeRows r54 :=
  eval_inv TwoCoreCentralizerData.eval_w14 product_58

theorem eval_v84 : toMatrix v84 = decodeRows r66 :=
  eval_mul TwoCoreCentralizerData.eval_w10 eval_v83 product_68

theorem eval_v85 : toMatrix v85 = decodeRows r67 :=
  eval_mul eval_v84 TwoCoreCentralizerData.eval_w10 product_69

theorem eval_v86 : toMatrix v86 = decodeRows r68 :=
  eval_mul eval_v85 TwoCoreCentralizerData.eval_w14 product_70

theorem eval_v87 : toMatrix v87 = decodeRows r69 :=
  eval_mul eval_v86 TwoCoreCentralizerData.eval_w10 product_71

theorem eval_v88 : toMatrix v88 = decodeRows r70 :=
  eval_mul eval_v87 TwoCoreCentralizerData.eval_w14 product_72

theorem eval_v89 : toMatrix v89 = decodeRows r71 :=
  eval_mul eval_v88 TwoCoreCentralizerData.eval_w10 product_73

theorem eval_v90 : toMatrix v90 = decodeRows r72 :=
  eval_mul eval_v89 TwoCoreCentralizerData.eval_w14 product_74

theorem eval_v91 : toMatrix v91 = decodeRows r73 :=
  eval_mul eval_v90 TwoCoreCentralizerData.eval_w10 product_75

theorem eval_v92 : toMatrix v92 = decodeRows r74 :=
  eval_mul eval_v91 eval_v83 product_76

theorem eval_v93 : toMatrix v93 = decodeRows r75 :=
  eval_mul eval_v92 TwoCoreCentralizerData.eval_w10 product_77

theorem eval_v94 : toMatrix v94 = decodeRows r76 :=
  eval_mul eval_v93 TwoCoreCentralizerData.eval_w14 product_78

theorem eval_v95 : toMatrix v95 = decodeRows r77 :=
  eval_mul eval_v94 TwoCoreCentralizerData.eval_w10 product_79

theorem eval_v96 : toMatrix v96 = decodeRows r78 :=
  eval_mul eval_v95 eval_v83 product_80

theorem eval_v97 : toMatrix v97 = decodeRows r66 :=
  eval_mul TwoCoreCentralizerData.eval_w10 eval_v83 product_68

theorem eval_v98 : toMatrix v98 = decodeRows r67 :=
  eval_mul eval_v97 TwoCoreCentralizerData.eval_w10 product_69

theorem eval_v99 : toMatrix v99 = decodeRows r68 :=
  eval_mul eval_v98 TwoCoreCentralizerData.eval_w14 product_70

theorem eval_v100 : toMatrix v100 = decodeRows r69 :=
  eval_mul eval_v99 TwoCoreCentralizerData.eval_w10 product_71

theorem eval_v101 : toMatrix v101 = decodeRows r79 :=
  eval_mul eval_v100 eval_v83 product_81

theorem eval_v102 : toMatrix v102 = decodeRows r80 :=
  eval_mul eval_v101 TwoCoreCentralizerData.eval_w10 product_82

theorem eval_v103 : toMatrix v103 = decodeRows r81 :=
  eval_mul eval_v102 eval_v83 product_83

theorem eval_v104 : toMatrix v104 = decodeRows r82 :=
  eval_mul eval_v103 TwoCoreCentralizerData.eval_w10 product_84

theorem eval_v105 : toMatrix v105 = decodeRows r83 :=
  eval_mul eval_v104 TwoCoreCentralizerData.eval_w14 product_85

theorem eval_v106 : toMatrix v106 = decodeRows r84 :=
  eval_mul eval_v105 TwoCoreCentralizerData.eval_w10 product_86

theorem eval_v107 : toMatrix v107 = decodeRows r85 :=
  eval_mul eval_v106 eval_v83 product_87

theorem eval_v108 : toMatrix v108 = decodeRows r86 :=
  eval_mul eval_v107 TwoCoreCentralizerData.eval_w10 product_88

theorem eval_v109 : toMatrix v109 = decodeRows r87 :=
  eval_mul eval_v108 eval_v83 product_89

theorem eval_v110 : toMatrix v110 = decodeRows r88 :=
  eval_mul eval_v109 TwoCoreCentralizerData.eval_w10 product_90

theorem eval_v111 : toMatrix v111 = decodeRows r89 :=
  eval_mul eval_v110 eval_v83 product_91

theorem eval_v112 : toMatrix v112 = decodeRows r90 :=
  eval_mul eval_v111 TwoCoreCentralizerData.eval_w10 product_92

theorem eval_v113 : toMatrix v113 = decodeRows r91 :=
  eval_mul eval_v112 TwoCoreCentralizerData.eval_w14 product_93

theorem eval_v114 : toMatrix v114 = decodeRows r92 :=
  eval_mul eval_v113 TwoCoreCentralizerData.eval_w10 product_94

theorem eval_v115 : toMatrix v115 = decodeRows r93 :=
  eval_mul eval_v114 eval_v83 product_95
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
