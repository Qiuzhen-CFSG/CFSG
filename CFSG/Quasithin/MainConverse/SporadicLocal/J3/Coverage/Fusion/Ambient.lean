module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes0To3
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes4To7
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes8To11
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes12To15
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes16To19
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes20To23
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient.Classes24To27
import Mathlib.Tactic.FinCases

/-!
# The 28 ambient fusion conjugators in J₃

The fixed words conjugate the selected generators of each elementary
representative to the indices prescribed in `Fusion/ClassData.lean`.
The descendants certify 46 commuting squares using packed maps checked
against the actual words on all 6156 letters. The other 12 identities
have empty conjugator words and follow by definitional equality.

This is the unconditional generator certificate for the parent fusion
assembly. Its orientation is Sylow class = conjugate of fixed representative.

Source: GLS, Number 3, Table 5.3h, printed p.269; the retained ATLAS J₃ model.
The five elementary representatives are intermediate groups for the coverage
argument, rather than an additional assertion of the source table.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
open Sporadic.Janko3.TwoLocal

/-- All 58 required generator identities for the fixed ambient conjugators. -/
public theorem ambient_generator_images (c : Fin 28) (j : Fin 4)
    (hj : j ∈ representativeBasis (alignedClass c)) :
    (MulAut.conj (ambientConjugator c)) (elementaryGenerator j) =
      element (generatorImage c j) := by
  fin_cases c
  · exact ambient_generator_images_0 j hj
  · exact ambient_generator_images_1 j hj
  · exact ambient_generator_images_2 j hj
  · exact ambient_generator_images_3 j hj
  · exact ambient_generator_images_4 j hj
  · exact ambient_generator_images_5 j hj
  · exact ambient_generator_images_6 j hj
  · exact ambient_generator_images_7 j hj
  · exact ambient_generator_images_8 j hj
  · exact ambient_generator_images_9 j hj
  · exact ambient_generator_images_10 j hj
  · exact ambient_generator_images_11 j hj
  · exact ambient_generator_images_12 j hj
  · exact ambient_generator_images_13 j hj
  · exact ambient_generator_images_14 j hj
  · exact ambient_generator_images_15 j hj
  · exact ambient_generator_images_16 j hj
  · exact ambient_generator_images_17 j hj
  · exact ambient_generator_images_18 j hj
  · exact ambient_generator_images_19 j hj
  · exact ambient_generator_images_20 j hj
  · exact ambient_generator_images_21 j hj
  · exact ambient_generator_images_22 j hj
  · exact ambient_generator_images_23 j hj
  · exact ambient_generator_images_24 j hj
  · exact ambient_generator_images_25 j hj
  · exact ambient_generator_images_26 j hj
  · exact ambient_generator_images_27 j hj

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.Fusion
