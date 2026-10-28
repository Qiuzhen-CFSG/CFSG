module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.Orbit

/-!
# A certified fixed vector for the ATLAS local subgroup of J₄

The base vector is fixed by both outputs of `max1Program`. For the first
output, we exhibit a row fixed by `a` whose image under `ab` is the base
vector. For the second, we exhibit a row fixed by `(ababab²)⁸` whose image
under `ab³` is the base vector. Conjugation then proves both assertions.

The 59 single-generator row products are checked by `decide +kernel` against
the source matrices; the packed rows are data, not external proof assumptions.
The resulting subgroup inclusion uses closure minimality. We also check that
`b` moves the base vector, so the vector stabilizer is proper. No group order
or simplicity theorem is used.

Sources: the representation and subgroup program documented in `Model.Data`
and `Cardinality.Subgroup`, respectively:
https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/J4G1-f2r112B0 and
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max1W1 .
-/

namespace Janko4.Cardinality

private def packedVector (n : ℕ) : CosetVector :=
  fun j => if n.testBit j.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep0 :
    Matrix.vecMul (packedVector 2822552807404317007234639603388789) matrixA =
      packedVector 2822552807404317007234639603388789 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep1 :
    Matrix.vecMul (packedVector 2822552807404317007234639603388789) matrixB =
      packedVector 1383886125678978288045195946262397 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep2 :
    Matrix.vecMul (packedVector 2263847150312364578077950221283724) matrixA =
      packedVector 1094963804767316245464432037218906 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep3 :
    Matrix.vecMul (packedVector 1094963804767316245464432037218906) matrixB =
      packedVector 4950987583656207227590743031890060 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep4 :
    Matrix.vecMul (packedVector 4950987583656207227590743031890060) matrixA =
      packedVector 90984545608135285627729146384983 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep5 :
    Matrix.vecMul (packedVector 90984545608135285627729146384983) matrixB =
      packedVector 4038162338237735914062747296603593 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep6 :
    Matrix.vecMul (packedVector 4038162338237735914062747296603593) matrixA =
      packedVector 1418111807550705559479306935904186 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep7 :
    Matrix.vecMul (packedVector 1418111807550705559479306935904186) matrixB =
      packedVector 999219271043543843868954312122610 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep8 :
    Matrix.vecMul (packedVector 999219271043543843868954312122610) matrixB =
      packedVector 1548698239058517465627222649628601 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep9 :
    Matrix.vecMul (packedVector 1548698239058517465627222649628601) matrixA =
      packedVector 4964798580612214776390173566041161 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep10 :
    Matrix.vecMul (packedVector 4964798580612214776390173566041161) matrixB =
      packedVector 3455316327446957283611251688143636 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep11 :
    Matrix.vecMul (packedVector 3455316327446957283611251688143636) matrixA =
      packedVector 466261888653994296361021495055325 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep12 :
    Matrix.vecMul (packedVector 466261888653994296361021495055325) matrixB =
      packedVector 2726480173724090064640656694680318 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep13 :
    Matrix.vecMul (packedVector 2726480173724090064640656694680318) matrixA =
      packedVector 548812176898182327445373415354246 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep14 :
    Matrix.vecMul (packedVector 548812176898182327445373415354246) matrixB =
      packedVector 2270492568540592056347010879471588 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep15 :
    Matrix.vecMul (packedVector 2270492568540592056347010879471588) matrixB =
      packedVector 4841092608456550446304526659323583 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep16 :
    Matrix.vecMul (packedVector 4841092608456550446304526659323583) matrixA =
      packedVector 2007831423212702757555271572719830 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep17 :
    Matrix.vecMul (packedVector 2007831423212702757555271572719830) matrixB =
      packedVector 2662173165678400858474178134593672 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep18 :
    Matrix.vecMul (packedVector 2662173165678400858474178134593672) matrixA =
      packedVector 245446179878371749590636976090828 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep19 :
    Matrix.vecMul (packedVector 245446179878371749590636976090828) matrixB =
      packedVector 5042886514581695184143845006516538 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep20 :
    Matrix.vecMul (packedVector 5042886514581695184143845006516538) matrixA =
      packedVector 5049095795285321078151205519875255 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep21 :
    Matrix.vecMul (packedVector 5049095795285321078151205519875255) matrixB =
      packedVector 1370598859247247745740838155493648 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep22 :
    Matrix.vecMul (packedVector 1370598859247247745740838155493648) matrixB =
      packedVector 449760563994466602772971938470027 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep23 :
    Matrix.vecMul (packedVector 449760563994466602772971938470027) matrixA =
      packedVector 4046310328483289458807591482750985 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep24 :
    Matrix.vecMul (packedVector 4046310328483289458807591482750985) matrixB =
      packedVector 5089478732948393651798577426116292 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep25 :
    Matrix.vecMul (packedVector 5089478732948393651798577426116292) matrixA =
      packedVector 4139421980062767448705564226832386 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep26 :
    Matrix.vecMul (packedVector 4139421980062767448705564226832386) matrixB =
      packedVector 1330110516144501507621018386970113 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep27 :
    Matrix.vecMul (packedVector 1330110516144501507621018386970113) matrixA =
      packedVector 2730227764350745985303283607735575 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep28 :
    Matrix.vecMul (packedVector 2730227764350745985303283607735575) matrixB =
      packedVector 3568985733509904542465670832674972 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep29 :
    Matrix.vecMul (packedVector 3568985733509904542465670832674972) matrixB =
      packedVector 2843993421139783629440194494962180 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep30 :
    Matrix.vecMul (packedVector 2843993421139783629440194494962180) matrixA =
      packedVector 3433370535371401623980649892420165 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep31 :
    Matrix.vecMul (packedVector 3433370535371401623980649892420165) matrixB =
      packedVector 13029449609703057651177100006742 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep32 :
    Matrix.vecMul (packedVector 13029449609703057651177100006742) matrixA =
      packedVector 4456386759552548483076044685377704 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep33 :
    Matrix.vecMul (packedVector 4456386759552548483076044685377704) matrixB =
      packedVector 2606493890649364850634359441165559 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep34 :
    Matrix.vecMul (packedVector 2606493890649364850634359441165559) matrixA =
      packedVector 2641058412841203512429618333216357 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep35 :
    Matrix.vecMul (packedVector 2641058412841203512429618333216357) matrixB =
      packedVector 1678790898916135937606020732909946 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep36 :
    Matrix.vecMul (packedVector 1678790898916135937606020732909946) matrixB =
      packedVector 2876601436552054475717781331956759 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep37 :
    Matrix.vecMul (packedVector 2876601436552054475717781331956759) matrixA =
      packedVector 2954088988480126542432842790900968 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep38 :
    Matrix.vecMul (packedVector 2954088988480126542432842790900968) matrixB =
      packedVector 1820200251206208177458189012786393 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep39 :
    Matrix.vecMul (packedVector 1820200251206208177458189012786393) matrixA =
      packedVector 3151135233330454966168417778363297 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep40 :
    Matrix.vecMul (packedVector 3151135233330454966168417778363297) matrixB =
      packedVector 3315532766301370847571369681302794 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep41 :
    Matrix.vecMul (packedVector 3315532766301370847571369681302794) matrixA =
      packedVector 4087951404661494222638471980335098 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep42 :
    Matrix.vecMul (packedVector 4087951404661494222638471980335098) matrixB =
      packedVector 3358262793268987070404599172675090 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep43 :
    Matrix.vecMul (packedVector 3358262793268987070404599172675090) matrixB =
      packedVector 4198488990952512029223717574551765 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep44 :
    Matrix.vecMul (packedVector 4198488990952512029223717574551765) matrixA =
      packedVector 967200985370995977360357509105685 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep45 :
    Matrix.vecMul (packedVector 967200985370995977360357509105685) matrixB =
      packedVector 1490485092959505570320799298659822 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep46 :
    Matrix.vecMul (packedVector 1490485092959505570320799298659822) matrixA =
      packedVector 3688723512487383899640487491841367 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep47 :
    Matrix.vecMul (packedVector 3688723512487383899640487491841367) matrixB =
      packedVector 4020983959767130520296852403896885 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep48 :
    Matrix.vecMul (packedVector 4020983959767130520296852403896885) matrixA =
      packedVector 3798345427094355410909965443128730 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep49 :
    Matrix.vecMul (packedVector 3798345427094355410909965443128730) matrixB =
      packedVector 5188996808349248953821623239427081 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep50 :
    Matrix.vecMul (packedVector 5188996808349248953821623239427081) matrixB =
      packedVector 584516553695521099369389657901358 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep51 :
    Matrix.vecMul (packedVector 584516553695521099369389657901358) matrixA =
      packedVector 4473492897267230619576204689568545 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep52 :
    Matrix.vecMul (packedVector 4473492897267230619576204689568545) matrixB =
      packedVector 5079013174777454149357601842837776 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep53 :
    Matrix.vecMul (packedVector 5079013174777454149357601842837776) matrixA =
      packedVector 1178574387878641948922336449998601 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep54 :
    Matrix.vecMul (packedVector 1178574387878641948922336449998601) matrixB =
      packedVector 2555869346145295475455838549044972 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep55 :
    Matrix.vecMul (packedVector 2555869346145295475455838549044972) matrixA =
      packedVector 194050638765324618144411446050940 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep56 :
    Matrix.vecMul (packedVector 194050638765324618144411446050940) matrixB =
      packedVector 3078997596362056165525093682341314 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep57 :
    Matrix.vecMul (packedVector 3078997596362056165525093682341314) matrixB =
      packedVector 2263847150312364578077950221283724 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem packedStep58 :
    Matrix.vecMul (packedVector 4950987583656207227590743031890060) matrixB =
      packedVector 2822552807404317007234639603388789 := by
  decide +kernel

private theorem vectorRight_conjugate_fixed (w : CosetVector) (u t : Model)
    (hu : vectorRight w u = w) :
    vectorRight (vectorRight w t) (t⁻¹ * u * t) = vectorRight w t := by
  rw [← vectorRight_mul]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, vectorRight_mul, hu]

private theorem first_output_fixes
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    vectorRight cosetBaseVector (max1Program (sourceA hA) (sourceB hB)).1 =
      cosetBaseVector := by
  let w := packedVector 2822552807404317007234639603388789
  have ha : vectorRight w (sourceA hA) = w := packedStep0
  have hb : vectorRight w (sourceB hB) = cosetBaseVector := packedStep1
  have ht : vectorRight w (sourceA hA * sourceB hB) = cosetBaseVector := by
    rw [vectorRight_mul, ha, hb]
  rw [max1Program_fst, ← ht]
  exact vectorRight_conjugate_fixed w _ _ ha

set_option maxRecDepth 10000 in
private theorem second_output_fixes
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    vectorRight cosetBaseVector (max1Program (sourceA hA) (sourceB hB)).2 =
      cosetBaseVector := by
  let w := packedVector 2263847150312364578077950221283724
  have hu : vectorRight w
      ((sourceA hA * sourceB hB * sourceA hA * sourceB hB * sourceA hA *
        sourceB hB ^ 2) ^ 8) = w := by
    simp only [pow_succ, pow_zero, vectorRight_mul, vectorRight_one]
    change _ = packedVector 2263847150312364578077950221283724
    simp only [vectorRight, toMatrix_sourceA, toMatrix_sourceB]
    dsimp only [w]
    rw [packedStep2, packedStep3, packedStep4, packedStep5, packedStep6, packedStep7,
      packedStep8, packedStep9, packedStep10, packedStep11, packedStep12, packedStep13,
      packedStep14, packedStep15, packedStep16, packedStep17, packedStep18, packedStep19,
      packedStep20, packedStep21, packedStep22, packedStep23, packedStep24, packedStep25,
      packedStep26, packedStep27, packedStep28, packedStep29, packedStep30, packedStep31,
      packedStep32, packedStep33, packedStep34, packedStep35, packedStep36, packedStep37,
      packedStep38, packedStep39, packedStep40, packedStep41, packedStep42, packedStep43,
      packedStep44, packedStep45, packedStep46, packedStep47, packedStep48, packedStep49,
      packedStep50, packedStep51, packedStep52, packedStep53, packedStep54, packedStep55,
      packedStep56, packedStep57]
  have ht : vectorRight w (sourceA hA * sourceB hB ^ 3) = cosetBaseVector := by
    simp only [pow_succ, pow_zero, vectorRight_mul, vectorRight_one]
    simp only [vectorRight, toMatrix_sourceA, toMatrix_sourceB]
    dsimp only [w]
    rw [packedStep2, packedStep3, packedStep58, packedStep1]
    rfl
  rw [max1Program_snd, ← ht]
  exact vectorRight_conjugate_fixed w _ _ hu

/-- Both literal subgroup-program outputs fix the specified binary row vector.
The finite vector computations above are checked by the Lean kernel. -/
public theorem max1Subgroup_le_cosetVectorStabilizer
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    max1Subgroup hA hB ≤ cosetVectorStabilizer := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact first_output_fixes hA hB
  · exact second_output_fixes hA hB

/-- The base vector has nonzero zeroth coordinate. -/
public theorem cosetBaseVector_ne_zero : cosetBaseVector ≠ 0 := by
  have h : cosetBaseVector 0 ≠ (0 : ZMod 2) := by decide +kernel
  exact fun he => h (congrFun he 0)

/-- The second source generator moves the base vector, so its stabilizer is
proper in the concrete matrix group. -/
public theorem sourceB_not_mem_cosetVectorStabilizer (hB : matrixB ^ 4 = 1) :
    sourceB hB ∉ cosetVectorStabilizer := by
  have h : Matrix.vecMul cosetBaseVector matrixB 0 ≠ cosetBaseVector 0 := by
    decide +kernel
  intro he
  change vectorRight cosetBaseVector (sourceB hB) = cosetBaseVector at he
  exact h (congrFun he 0)

end Janko4.Cardinality
