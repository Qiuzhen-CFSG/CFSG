module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Certificates
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Soundness

/-!
# The six long relations on the literal degree-1408 matrices

All six identities are unconditional. Forty-six shared matrix products are
checked by kernel reduction and identified with the ordinary matrix products
by `LongPacked.productCertificate_sound`. The final expressions reduce to the
existing source lists at indices 7–12, in their original multiplication order.
They include all of R1, R2 and R3; in particular R1 uses a shared square.
No other branch of the matrix-relation certificate is assumed.

Source: the retained ATLAS HSG1-P1.M in `Descent/source/`, with unchanged
signed words in `Descent.Words` and alphabet in `MatrixRelations.Checker`.
See `LongWords/source/README.md` for generation, attribution and measurements.
-/

namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
open Thompson.BinaryMatrix
open LongPacked

private def word0 : List (Fin 4) := [0]

private theorem eval0 : (word0.map letterMatrix).prod = decode 1408 aRows := by
  simp only [word0, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def word1 : List (Fin 4) := [1]

private theorem eval1 : (word1.map letterMatrix).prod = decode 1408 bRows := by
  simp only [word1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def word3 : List (Fin 4) := [3]

private theorem eval3 : (word3.map letterMatrix).prod = decode 1408 inverseRows := by
  simp only [word3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private def word4 : List (Fin 4) := word0 ++ word1

private theorem eval4 : (word4.map letterMatrix).prod = decode 1408 rows4 := by
  rw [word4, List.map_append, List.prod_append, eval0, eval1]
  exact productCertificate_sound _ _ _ bounded0 bounded1 bounded4 size1 certificate4

private def word5 : List (Fin 4) := word4 ++ word4

private theorem eval5 : (word5.map letterMatrix).prod = decode 1408 rows5 := by
  rw [word5, List.map_append, List.prod_append, eval4]
  exact productCertificate_sound _ _ _ bounded4 bounded4 bounded5 size4 certificate5

private def word6 : List (Fin 4) := word0 ++ word3

private theorem eval6 : (word6.map letterMatrix).prod = decode 1408 rows6 := by
  rw [word6, List.map_append, List.prod_append, eval0, eval3]
  exact productCertificate_sound _ _ _ bounded0 bounded3 bounded6 size3 certificate6

private def word7 : List (Fin 4) := word4 ++ word1

private theorem eval7 : (word7.map letterMatrix).prod = decode 1408 rows7 := by
  rw [word7, List.map_append, List.prod_append, eval4, eval1]
  exact productCertificate_sound _ _ _ bounded4 bounded1 bounded7 size1 certificate7

private def word8 : List (Fin 4) := word6 ++ word3

private theorem eval8 : (word8.map letterMatrix).prod = decode 1408 rows8 := by
  rw [word8, List.map_append, List.prod_append, eval6, eval3]
  exact productCertificate_sound _ _ _ bounded6 bounded3 bounded8 size3 certificate8

private def word9 : List (Fin 4) := word5 ++ word7

private theorem eval9 : (word9.map letterMatrix).prod = decode 1408 rows9 := by
  rw [word9, List.map_append, List.prod_append, eval5, eval7]
  exact productCertificate_sound _ _ _ bounded5 bounded7 bounded9 size7 certificate9

private def word10 : List (Fin 4) := word8 ++ word8

private theorem eval10 : (word10.map letterMatrix).prod = decode 1408 rows10 := by
  rw [word10, List.map_append, List.prod_append, eval8]
  exact productCertificate_sound _ _ _ bounded8 bounded8 bounded10 size8 certificate10

private def word11 : List (Fin 4) := word5 ++ word1

private theorem eval11 : (word11.map letterMatrix).prod = decode 1408 rows11 := by
  rw [word11, List.map_append, List.prod_append, eval5, eval1]
  exact productCertificate_sound _ _ _ bounded5 bounded1 bounded11 size1 certificate11

private def word12 : List (Fin 4) := word9 ++ word6

private theorem eval12 : (word12.map letterMatrix).prod = decode 1408 rows12 := by
  rw [word12, List.map_append, List.prod_append, eval9, eval6]
  exact productCertificate_sound _ _ _ bounded9 bounded6 bounded12 size6 certificate12

private def word13 : List (Fin 4) := word6 ++ word7

private theorem eval13 : (word13.map letterMatrix).prod = decode 1408 rows13 := by
  rw [word13, List.map_append, List.prod_append, eval6, eval7]
  exact productCertificate_sound _ _ _ bounded6 bounded7 bounded13 size7 certificate13

private def word14 : List (Fin 4) := word5 ++ word6

private theorem eval14 : (word14.map letterMatrix).prod = decode 1408 rows14 := by
  rw [word14, List.map_append, List.prod_append, eval5, eval6]
  exact productCertificate_sound _ _ _ bounded5 bounded6 bounded14 size6 certificate14

private def word15 : List (Fin 4) := word12 ++ word8

private theorem eval15 : (word15.map letterMatrix).prod = decode 1408 rows15 := by
  rw [word15, List.map_append, List.prod_append, eval12, eval8]
  exact productCertificate_sound _ _ _ bounded12 bounded8 bounded15 size8 certificate15

private def word16 : List (Fin 4) := word10 ++ word7

private theorem eval16 : (word16.map letterMatrix).prod = decode 1408 rows16 := by
  rw [word16, List.map_append, List.prod_append, eval10, eval7]
  exact productCertificate_sound _ _ _ bounded10 bounded7 bounded16 size7 certificate16

private def word17 : List (Fin 4) := word9 ++ word7

private theorem eval17 : (word17.map letterMatrix).prod = decode 1408 rows17 := by
  rw [word17, List.map_append, List.prod_append, eval9, eval7]
  exact productCertificate_sound _ _ _ bounded9 bounded7 bounded17 size7 certificate17

private def word18 : List (Fin 4) := word15 ++ word14

private theorem eval18 : (word18.map letterMatrix).prod = decode 1408 rows18 := by
  rw [word18, List.map_append, List.prod_append, eval15, eval14]
  exact productCertificate_sound _ _ _ bounded15 bounded14 bounded18 size14 certificate18

private def word19 : List (Fin 4) := word15 ++ word13

private theorem eval19 : (word19.map letterMatrix).prod = decode 1408 rows19 := by
  rw [word19, List.map_append, List.prod_append, eval15, eval13]
  exact productCertificate_sound _ _ _ bounded15 bounded13 bounded19 size13 certificate19

private def word20 : List (Fin 4) := word19 ++ word5

private theorem eval20 : (word20.map letterMatrix).prod = decode 1408 rows20 := by
  rw [word20, List.map_append, List.prod_append, eval19, eval5]
  exact productCertificate_sound _ _ _ bounded19 bounded5 bounded20 size5 certificate20

private def word21 : List (Fin 4) := word20 ++ word10

private theorem eval21 : (word21.map letterMatrix).prod = decode 1408 rows21 := by
  rw [word21, List.map_append, List.prod_append, eval20, eval10]
  exact productCertificate_sound _ _ _ bounded20 bounded10 bounded21 size10 certificate21

private def word22 : List (Fin 4) := word21 ++ word10

private theorem eval22 : (word22.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word22, List.map_append, List.prod_append, eval21, eval10]
  exact productCertificate_sound _ _ _ bounded21 bounded10 identity_bounded size10 certificate22

private def word23 : List (Fin 4) := word11 ++ word16

private theorem eval23 : (word23.map letterMatrix).prod = decode 1408 rows23 := by
  rw [word23, List.map_append, List.prod_append, eval11, eval16]
  exact productCertificate_sound _ _ _ bounded11 bounded16 bounded23 size16 certificate23

private def word24 : List (Fin 4) := word23 ++ word16

private theorem eval24 : (word24.map letterMatrix).prod = decode 1408 rows24 := by
  rw [word24, List.map_append, List.prod_append, eval23, eval16]
  exact productCertificate_sound _ _ _ bounded23 bounded16 bounded24 size16 certificate24

private def word25 : List (Fin 4) := word24 ++ word11

private theorem eval25 : (word25.map letterMatrix).prod = decode 1408 rows25 := by
  rw [word25, List.map_append, List.prod_append, eval24, eval11]
  exact productCertificate_sound _ _ _ bounded24 bounded11 bounded25 size11 certificate25

private def word26 : List (Fin 4) := word25 ++ word13

private theorem eval26 : (word26.map letterMatrix).prod = decode 1408 rows26 := by
  rw [word26, List.map_append, List.prod_append, eval25, eval13]
  exact productCertificate_sound _ _ _ bounded25 bounded13 bounded26 size13 certificate26

private def word27 : List (Fin 4) := word26 ++ word13

private theorem eval27 : (word27.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word27, List.map_append, List.prod_append, eval26, eval13]
  exact productCertificate_sound _ _ _ bounded26 bounded13 identity_bounded size13 certificate27

private def word28 : List (Fin 4) := word17 ++ word4

private theorem eval28 : (word28.map letterMatrix).prod = decode 1408 rows28 := by
  rw [word28, List.map_append, List.prod_append, eval17, eval4]
  exact productCertificate_sound _ _ _ bounded17 bounded4 bounded28 size4 certificate28

private def word29 : List (Fin 4) := word28 ++ word6

private theorem eval29 : (word29.map letterMatrix).prod = decode 1408 rows29 := by
  rw [word29, List.map_append, List.prod_append, eval28, eval6]
  exact productCertificate_sound _ _ _ bounded28 bounded6 bounded29 size6 certificate29

private def word30 : List (Fin 4) := word29 ++ word6

private theorem eval30 : (word30.map letterMatrix).prod = decode 1408 rows30 := by
  rw [word30, List.map_append, List.prod_append, eval29, eval6]
  exact productCertificate_sound _ _ _ bounded29 bounded6 bounded30 size6 certificate30

private def word31 : List (Fin 4) := word30 ++ word11

private theorem eval31 : (word31.map letterMatrix).prod = decode 1408 rows31 := by
  rw [word31, List.map_append, List.prod_append, eval30, eval11]
  exact productCertificate_sound _ _ _ bounded30 bounded11 bounded31 size11 certificate31

private def word32 : List (Fin 4) := word31 ++ word7

private theorem eval32 : (word32.map letterMatrix).prod = decode 1408 rows32 := by
  rw [word32, List.map_append, List.prod_append, eval31, eval7]
  exact productCertificate_sound _ _ _ bounded31 bounded7 bounded32 size7 certificate32

private def word33 : List (Fin 4) := word32 ++ word5

private theorem eval33 : (word33.map letterMatrix).prod = decode 1408 rows33 := by
  rw [word33, List.map_append, List.prod_append, eval32, eval5]
  exact productCertificate_sound _ _ _ bounded32 bounded5 bounded33 size5 certificate33

private def word34 : List (Fin 4) := word33 ++ word8

private theorem eval34 : (word34.map letterMatrix).prod = decode 1408 rows34 := by
  rw [word34, List.map_append, List.prod_append, eval33, eval8]
  exact productCertificate_sound _ _ _ bounded33 bounded8 bounded34 size8 certificate34

private def word35 : List (Fin 4) := word34 ++ word6

private theorem eval35 : (word35.map letterMatrix).prod = decode 1408 rows35 := by
  rw [word35, List.map_append, List.prod_append, eval34, eval6]
  exact productCertificate_sound _ _ _ bounded34 bounded6 bounded35 size6 certificate35

private def word36 : List (Fin 4) := word35 ++ word8

private theorem eval36 : (word36.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word36, List.map_append, List.prod_append, eval35, eval8]
  exact productCertificate_sound _ _ _ bounded35 bounded8 identity_bounded size8 certificate36

private def word37 : List (Fin 4) := word18 ++ word18

private theorem eval37 : (word37.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word37, List.map_append, List.prod_append, eval18]
  exact productCertificate_sound _ _ _ bounded18 bounded18 identity_bounded size18 certificate37

private def word38 : List (Fin 4) := word9 ++ word9

private theorem eval38 : (word38.map letterMatrix).prod = decode 1408 rows38 := by
  rw [word38, List.map_append, List.prod_append, eval9]
  exact productCertificate_sound _ _ _ bounded9 bounded9 bounded38 size9 certificate38

private def word39 : List (Fin 4) := word38 ++ word14

private theorem eval39 : (word39.map letterMatrix).prod = decode 1408 rows39 := by
  rw [word39, List.map_append, List.prod_append, eval38, eval14]
  exact productCertificate_sound _ _ _ bounded38 bounded14 bounded39 size14 certificate39

private def word40 : List (Fin 4) := word39 ++ word17

private theorem eval40 : (word40.map letterMatrix).prod = decode 1408 rows40 := by
  rw [word40, List.map_append, List.prod_append, eval39, eval17]
  exact productCertificate_sound _ _ _ bounded39 bounded17 bounded40 size17 certificate40

private def word41 : List (Fin 4) := word40 ++ word7

private theorem eval41 : (word41.map letterMatrix).prod = decode 1408 rows41 := by
  rw [word41, List.map_append, List.prod_append, eval40, eval7]
  exact productCertificate_sound _ _ _ bounded40 bounded7 bounded41 size7 certificate41

private def word42 : List (Fin 4) := word41 ++ word14

private theorem eval42 : (word42.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word42, List.map_append, List.prod_append, eval41, eval14]
  exact productCertificate_sound _ _ _ bounded41 bounded14 identity_bounded size14 certificate42

private def word43 : List (Fin 4) := word9 ++ word11

private theorem eval43 : (word43.map letterMatrix).prod = decode 1408 rows43 := by
  rw [word43, List.map_append, List.prod_append, eval9, eval11]
  exact productCertificate_sound _ _ _ bounded9 bounded11 bounded43 size11 certificate43

private def word44 : List (Fin 4) := word43 ++ word11

private theorem eval44 : (word44.map letterMatrix).prod = decode 1408 rows44 := by
  rw [word44, List.map_append, List.prod_append, eval43, eval11]
  exact productCertificate_sound _ _ _ bounded43 bounded11 bounded44 size11 certificate44

private def word45 : List (Fin 4) := word44 ++ word12

private theorem eval45 : (word45.map letterMatrix).prod = decode 1408 rows45 := by
  rw [word45, List.map_append, List.prod_append, eval44, eval12]
  exact productCertificate_sound _ _ _ bounded44 bounded12 bounded45 size12 certificate45

private def word46 : List (Fin 4) := word45 ++ word4

private theorem eval46 : (word46.map letterMatrix).prod = decode 1408 rows46 := by
  rw [word46, List.map_append, List.prod_append, eval45, eval4]
  exact productCertificate_sound _ _ _ bounded45 bounded4 bounded46 size4 certificate46

private def word47 : List (Fin 4) := word46 ++ word8

private theorem eval47 : (word47.map letterMatrix).prod = decode 1408 rows47 := by
  rw [word47, List.map_append, List.prod_append, eval46, eval8]
  exact productCertificate_sound _ _ _ bounded46 bounded8 bounded47 size8 certificate47

private def word48 : List (Fin 4) := word47 ++ word4

private theorem eval48 : (word48.map letterMatrix).prod = decode 1408 rows48 := by
  rw [word48, List.map_append, List.prod_append, eval47, eval4]
  exact productCertificate_sound _ _ _ bounded47 bounded4 bounded48 size4 certificate48

private def word49 : List (Fin 4) := word48 ++ word13

private theorem eval49 : (word49.map letterMatrix).prod = decode 1408 identityRows := by
  rw [word49, List.map_append, List.prod_append, eval48, eval13]
  exact productCertificate_sound _ _ _ bounded48 bounded13 identity_bounded size13 certificate49

private theorem relation7 : matrixWord 7 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 7 = word22 := rfl
  rw [matrixWord, hword, eval22, identity_decode]

private theorem relation8 : matrixWord 8 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 8 = word27 := rfl
  rw [matrixWord, hword, eval27, identity_decode]

private theorem relation9 : matrixWord 9 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 9 = word36 := rfl
  rw [matrixWord, hword, eval36, identity_decode]

private theorem relation10 : matrixWord 10 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 10 = word37 := rfl
  rw [matrixWord, hword, eval37, identity_decode]

private theorem relation11 : matrixWord 11 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 11 = word42 := rfl
  rw [matrixWord, hword, eval42, identity_decode]

private theorem relation12 : matrixWord 12 = 1 := by
  have hword : Sporadic.LeechRelated.HS.AtlasPresentation.relatorLetters 12 = word49 := rfl
  rw [matrixWord, hword, eval49, identity_decode]

/-- Source indices 7–12, including all three additional ATLAS relations. -/
public theorem largeWords : ∀ i : Fin 6, matrixWord ⟨i.val + 7, by omega⟩ = 1 := by
  intro i
  fin_cases i
  · exact relation7
  · exact relation8
  · exact relation9
  · exact relation10
  · exact relation11
  · exact relation12

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
