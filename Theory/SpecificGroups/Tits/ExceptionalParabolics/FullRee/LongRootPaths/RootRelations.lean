module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.ShortCentralizer
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
-- Only the fixed relative-root comparison and its certified binary rows use
-- the internal realization. No private data appears in the exported statements.
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison.BinaryProducts

/-!
# The two order-four roots in the marked five-normalizer

The specified outer root q=u₁ and embedded s₅ commute, and both act by
exponent three on the literal rotation s₁r₁. Small binary matrix products
prove these identities and the fixed root comparison transports them to the
original full Ree carrier. Source: Aschbacher--Smith J.4.7, printed p.442.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations
open ReeF4 ReeF4.DerivedTits.Realization
open Tits.InvolutionRootGeometry.BinaryDerivedFusion
open TransportComparison Thompson.BinaryMatrix

private abbrev qB := Products.relative 0
private abbrev sB := Products.generator .s5
private def rB : Products.BinaryUnit := Products.generator .s1 * Products.generator .r1

private def rRows : Array ℕ := #[1, 32770, 49157, 8, 64, 128, 16777296, 33554592, 1024, 2048, 134217984, 67109376, 68719509504, 137438973952, 274877964299, 549755850753, 65536, 131136, 134479872, 524288, 16777216, 33554432, 67108864, 134217728, 1048640, 2097280, 71305216, 142607360, 17593528221696, 35187056443392, 268435456, 536870912, 140754668224512, 70403103916032, 4294967296, 8589934592, 4096, 40960, 16384, 32768, 1099511627776, 2199291691008, 145135534866432, 8796093022208, 281475245146112, 562950490292224, 1196277240954880, 2392541597007872, 17592186044416, 35184372088832, 70368744177664, 140737488355328]

private def r2Rows : Array ℕ := #[1, 549755817987, 824633765902, 8, 16777296, 33554592, 17825872, 35651744, 134217984, 67109376, 142606336, 71303168, 549755846657, 343597432843, 962072731649, 618475327488, 65536, 16908304, 8651776, 524288, 1048640, 2097280, 71305216, 142607360, 80, 160, 71305728, 142607616, 299068504932352, 598137009864704, 17593528221696, 35187056443392, 2392537302040576, 1196268651020288, 140754668224512, 70403103916032, 68719509504, 687194816513, 274877964299, 549755850753, 1099511627776, 19792283041792, 2256202155163648, 8796093022208, 1342177280, 2684354560, 1196311600693248, 2392558776877056, 281475245146112, 562950490292224, 1196277240954880, 2392541597007872]

private def r3Rows : Array ℕ := #[1, 68719509507, 755914293262, 8, 17825872, 35651744, 1048656, 2097312, 142606336, 71303168, 8389632, 4196352, 549755817984, 824633761793, 962072690699, 618475323393, 65536, 1179712, 134480128, 524288, 80, 160, 71305728, 142607616, 16777232, 33554464, 71303680, 142606592, 281476318887936, 562952637775872, 299068504932352, 598137009864704, 2251804108652544, 1125908496777216, 2392537302040576, 1196268651020288, 549755846657, 824633741323, 962072731649, 618475327488, 1099511627776, 283674268401664, 145152714735616, 8796093022208, 17593259786240, 35186519572480, 1196303010758656, 2392554481909760, 1342177280, 2684354560, 1196311600693248, 2392558776877056]

private def qs5Rows : Array ℕ := #[1, 1649267441666, 12920335368196, 1099511627784, 2251800887427088, 1125902054326304, 2674030801846352, 1759255650631840, 17180918016, 34361836032, 2251804133819408, 1125908534528032, 549755817984, 17936857178112, 282438391578635, 618475323393, 9895604715521, 2267194050347033, 2264993962065945, 8796093612033, 281492157628416, 562984315256832, 1125899911036960, 2251799822073872, 2269397385216016, 1161095049904160, 1196303084159648, 2392554625565008, 2674030800797696, 1759255648534528, 2251800887427072, 1125902054326272, 2251804108652544, 1125908496777216, 17179869184, 34359738368, 68719476736, 282162171478016, 275951648768, 549755813888, 9895604649984, 2267194050215936, 2264993953218560, 8796093022208, 2269397368438784, 1161095016349696, 1196303010758656, 2392554481909760, 281492156579840, 562984313159680, 1125899906842624, 2251799813685248]

private def qrRows : Array ℕ := #[1, 36866, 57349, 8, 64, 128, 17825872, 35651744, 134218752, 67110912, 1280, 2560, 68719480833, 137438998538, 481036365825, 618475327488, 65536, 16908352, 134480896, 524288, 16777280, 33554560, 67108864, 134217728, 17825792, 35651584, 71305728, 142607616, 299068504932352, 598137009864704, 268435456, 536870912, 21474836480, 42949672960, 140741783322624, 70377334112256, 36864, 24576, 49152, 32768, 1099511627776, 19791477735424, 145139829833728, 8796093022208, 299067162755072, 598134325510144, 1196311600693248, 2392558776877056, 17592454479872, 35184908959744, 70368744177664, 140737488355328]

private def s5rRows : Array ℕ := #[1, 1099511664642, 29687082442757, 1099511627784, 140737756790848, 70369281048704, 2691627299635280, 1794448646209696, 140741934318656, 70377434777728, 21492663552, 42985327104, 68719480833, 299204601753610, 299549541298177, 618475327488, 9895604715521, 173727417499721, 153936074310729, 8796093612033, 158334254579776, 105562276626560, 70368811286656, 140737622573120, 299088655417344, 598177310834688, 1196311707650720, 2392558937310544, 2691627281809408, 1794448610557952, 140737756790784, 70369281048576, 21474836480, 42949672960, 140741783322624, 70377334112256, 36864, 17592454504448, 268484608, 32768, 9895604649984, 173727400591360, 153935922855936, 8796093022208, 299088637591552, 598177275183104, 1196311600693248, 2392558776877056, 158334237802496, 105562243072000, 70368744177664, 140737488355328]

private theorem rval : decode 52 (Binary.generatorRows .s1) * decode 52 (Binary.generatorRows .r1) = decode 52 rRows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem r2val : decode 52 (rRows) * decode 52 (rRows) = decode 52 r2Rows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem r3val : decode 52 (r2Rows) * decode 52 (rRows) = decode 52 r3Rows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem qs5val : decode 52 (Products.relativeRows0) * decode 52 (Binary.generatorRows .s5) = decode 52 qs5Rows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem s5qval : decode 52 (Binary.generatorRows .s5) * decode 52 (Products.relativeRows0) = decode 52 qs5Rows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem qrval : decode 52 (Products.relativeRows0) * decode 52 (rRows) = decode 52 qrRows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem r3qval : decode 52 (r3Rows) * decode 52 (Products.relativeRows0) = decode 52 qrRows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem s5rval : decode 52 (Binary.generatorRows .s5) * decode 52 (rRows) = decode 52 s5rRows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem r3s5val : decode 52 (r3Rows) * decode 52 (Binary.generatorRows .s5) = decode 52 s5rRows :=
  decode_mul 52 _ _ _ (by decide +kernel)

private theorem rB_val : rB.val = decode 52 rRows := by
  simp only [rB, Units.val_mul, Products.generator_val, Binary.generatorMatrix]
  exact rval

attribute [local irreducible] rB

private theorem rB_cube_val : (rB^3).val = decode 52 r3Rows := by
  rw [pow_succ, pow_two]
  change (rB.val * rB.val) * rB.val = _
  rw [rB_val, r2val, r3val]

private theorem binary_commute : qB*sB = sB*qB := by
  apply Units.ext
  simp only [Units.val_mul, qB, sB, Products.relative_val_0,
    Products.generator_val, Binary.generatorMatrix, qs5val, s5qval]

private theorem binary_q_rotation : qB*rB = rB^3*qB := by
  apply Units.ext
  change qB.val * rB.val = (rB^3).val * qB.val
  rw [rB_val, rB_cube_val, Products.relative_val_0, qrval, r3qval]

private theorem binary_s_rotation : sB*rB = rB^3*sB := by
  apply Units.ext
  change sB.val * rB.val = (rB^3).val * sB.val
  rw [rB_val, rB_cube_val, Products.generator_val]
  change decode 52 (Binary.generatorRows .s5) * decode 52 rRows =
    decode 52 r3Rows * decode 52 (Binary.generatorRows .s5)
  rw [s5rval, r3s5val]

/-- The genuine outer relative-root element. -/
@[expose] def q : Model 0 := fixedU 0

/-- The specified derived order-four root word. -/
@[expose] def s : Model 0 := atlasEmbedding (atlas1600ParrottAssignment .s5)

private theorem renumber_injective (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52) :
    Function.Injective (renumber e) :=
  Units.map_injective (Matrix.reindexRingEquiv (CoefficientField 0) e).injective

private theorem q_comparison (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    renumber e (toSplitGroup 0 q).val = extendScalars qB := by
  rw [q, fixedU_matrix]
  exact compare_relative e h 0

private theorem s_comparison (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    renumber e (toSplitGroup 0 s).val = extendScalars sB := by
  rw [s, atlasEmbedding_generator_matrix]
  exact compare_generator e h .s5

private theorem r_comparison (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    renumber e (toSplitGroup 0 rotation).val = extendScalars rB := by
  change renumber e (toSplitGroup 0 (atlasEmbedding
    (atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1))).val = _
  simp only [map_mul, atlasEmbedding_generator_matrix, Subgroup.coe_mul,
    compare_generator e h, rB]

set_option maxRecDepth 20000 in
theorem q_commutes_s : Commute q s := by
  obtain ⟨e, h⟩ := exists_simpleMatrixComparison
  apply toSplitGroup_injective 0
  apply Subtype.ext
  apply renumber_injective e
  simpa only [map_mul, Subgroup.coe_mul, q_comparison e h, s_comparison e h] using
    congrArg extendScalars binary_commute

set_option maxRecDepth 20000 in
theorem q_rotation : q*rotation = rotation^3*q := by
  obtain ⟨e, h⟩ := exists_simpleMatrixComparison
  apply toSplitGroup_injective 0
  apply Subtype.ext
  apply renumber_injective e
  simpa only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
    q_comparison e h, r_comparison e h] using congrArg extendScalars binary_q_rotation

set_option maxRecDepth 20000 in
theorem s_rotation : s*rotation = rotation^3*s := by
  obtain ⟨e, h⟩ := exists_simpleMatrixComparison
  apply toSplitGroup_injective 0
  apply Subtype.ext
  apply renumber_injective e
  simpa only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
    s_comparison e h, r_comparison e h] using congrArg extendScalars binary_s_rotation

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations
