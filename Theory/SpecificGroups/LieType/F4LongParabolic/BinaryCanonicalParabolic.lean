module
public import Theory.SpecificGroups.LieType.F4LongParabolic.BinaryRadical
public import Theory.SpecificGroups.LieType.F4LongParabolic.Characteristic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# The canonical long-A2 parabolic in the original binary F4 coordinates

The field of order two and the Cartan-plus-root basis identify the canonical
split F4 matrices with the binary matrices used for the original-core action
calculation. Twenty-four positive root curves are certified by simple Weyl
conjugations and small packed-matrix products. Exhaustiveness uses the actual
48-root coordinate enumeration, retaining every root and its positive sign.

The resulting embedding sends the canonical long-A2 parabolic exactly to
P = E join A. Its positive subgroup U lies in P and contains E and the two
positive long simple roots. The comparison preserves this literal subgroup;
no quotient or classification is used. The Sylow and MS3 consumers are in
BinaryCanonicalSylow and MS93.OriginalAction.F4Input, respectively.

Sources: the integral Geck tables in A02ParabolicSections.SourceLevi.F4,
GLS3 1.12 and 2.6; the original/replacement distinction in Aschbacher--Smith
C.1.31--34, printed pp.135--137, and MS93's F4 examples, printed p.831.
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
open Theory.SpecificGroups.LieType.SourceLevi.F4
namespace Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates.Canonical
open ReeF4
local instance rootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def fieldEquiv : CoefficientField 0 ≃+* ZMod 2 :=
  (ZMod.ringEquiv (CoefficientField 0) (by simpa [← Nat.card_eq_fintype_card] using field_card 0)).symm

private def matrixEquiv : MatrixUnits 0 ≃* Matˣ :=
  Units.mapEquiv ((reindex (S := CoefficientField 0)).trans fieldEquiv.mapMatrix).toMulEquiv

def embedding : SplitGroup 0 →* Matˣ :=
  matrixEquiv.toMonoidHom.comp (SplitGroup 0).subtype

theorem embedding_injective : Function.Injective embedding :=
  matrixEquiv.injective.comp (SplitGroup 0).subtype_injective

private theorem positive_matrix (i : Fin 4) :
    (embedding (rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1)).val =
      (Matrices.positiveInteger i).map (Int.castRingHom (ZMod 2)) := by
  change (reindex (F4Chevalley.rootCurve (typeF4SimpleRootIndex i)
    (1 : CoefficientField 0)).val).map fieldEquiv = _
  change (reindex (rootCurveUnit integralChevalleyRootOperators
    (typeF4SimpleRootIndex i) (1 : CoefficientField 0)).val).map fieldEquiv = _
  rw [← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val,
    Matrices.positive_one]
  ext r c
  simp

private theorem negative_matrix (i : Fin 4) :
    (embedding (rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1)).val =
      (Matrices.negativeInteger i).map (Int.castRingHom (ZMod 2)) := by
  change (reindex (F4Chevalley.rootCurve (-typeF4SimpleRootIndex i)
    (1 : CoefficientField 0)).val).map fieldEquiv = _
  change (reindex (rootCurveUnit integralChevalleyRootOperators
    (-typeF4SimpleRootIndex i) (1 : CoefficientField 0)).val).map fieldEquiv = _
  rw [← typeF4RootPairing_baseEquiv_val, rootCurveUnit_neg_simple, negativeUnit_val,
    Matrices.negative_one]
  ext r c
  simp

open ReeF4.LocalBlockInput.PairNormalization
open ReeF4.WordRelations
open Thompson.BinaryMatrix

private lemma simple_conjugation (i : Fin 4) (r : F4Chevalley.Root) :
    simpleLift 0 i * rootGeneratorInGroup 0 r 1 * (simpleLift 0 i)⁻¹ =
      rootGeneratorInGroup 0 (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) 1 := by
  apply Subtype.ext
  change (F4Chevalley.rootCurve (typeF4SimpleRootIndex i) (1 : CoefficientField 0) *
      F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) 1 *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1) * F4Chevalley.rootCurve r 1 *
      (F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1 *
      F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) 1 *
      F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1)⁻¹ = _
  change _ = F4Chevalley.rootCurve _ (1 : CoefficientField 0)
  have hh := OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
    (typeF4RootPairing_baseEquiv i) r (1 : CoefficientField 0)
  simpa only [titsUnit_cons, titsUnit_nil, mul_one, CharTwo.neg_eq,
    typeF4RootPairing_baseEquiv_val] using hh

private lemma lift_inverse (i : Fin 4) : (simpleLift 0 i)⁻¹ = simpleLift 0 i := by
  have hi (r : F4Chevalley.Root) : (rootGeneratorInGroup 0 r 1)⁻¹ =
      rootGeneratorInGroup 0 r 1 := by
    apply Subtype.ext
    change (F4Chevalley.rootCurve r (1 : CoefficientField 0))⁻¹ = F4Chevalley.rootCurve r 1
    rw [F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  simp only [simpleLift, mul_inv_rev, hi, mul_assoc]

private lemma simple_reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val = r.val -
      ((if i.val < 2 then 1 else 2) * dot r.val (typeF4SimpleRoot i)) •
        typeF4SimpleRoot i := by
  rw [← typeF4RootPairing_root, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot]
  rfl

private lemma positive_integer (i : Fin 4) :
    Matrices.positiveInteger i = Matrices.integerGenerator ⟨2*i.val, by omega⟩ := by
  fin_cases i <;> norm_num only
  all_goals simp only [Matrices.integerGenerator, Matrix.cons_val, Fin.reduceFinMk]
private lemma negative_integer (i : Fin 4) :
    Matrices.negativeInteger i = Matrices.integerGenerator ⟨2*i.val+1, by omega⟩ := by
  fin_cases i <;> norm_num only
  all_goals simp only [Matrices.integerGenerator, Matrix.cons_val, Fin.reduceFinMk]
private lemma positive_decode (i : Fin 4) :
    (embedding (rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1)).val =
      decode 52 (WordCertificates.generatorRows ⟨2*i.val, by omega⟩) := by
  rw [positive_matrix, positive_integer]
  exact GeneratorTables.integer_cast_decode _

private lemma negative_decode (i : Fin 4) :
    (embedding (rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1)).val =
      decode 52 (WordCertificates.generatorRows ⟨2*i.val+1, by omega⟩) := by
  rw [negative_matrix, negative_integer]
  exact GeneratorTables.integer_cast_decode _
private def liftFirst0 : Array ℕ := #[33554435, 2, 4, 8, 16, 32, 320, 512, 64, 640, 1024, 2048, 69632, 131072, 278528, 524288, 4096, 139264, 16384, 557056, 1048576, 2097152, 4194304, 8388608, 16777216, 100663298, 33554432, 134217728, 4563402752, 9126805504, 17179869184, 34359738368, 268435456, 536870912, 18253611008, 36507222016, 68719476736, 137438953472, 1374389534720, 2748779069440, 274877906944, 549755813888, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 351843720888320, 703687441776640, 70368744177664, 140737488355328, 1125899906842624, 2251799813685248]
private def liftRows0 : Array ℕ := #[3, 2, 4, 8, 16, 32, 256, 512, 64, 128, 1024, 2048, 65536, 131072, 262144, 524288, 4096, 8192, 16384, 32768, 1048576, 2097152, 4194304, 8388608, 16777216, 67108864, 33554432, 134217728, 4294967296, 8589934592, 17179869184, 34359738368, 268435456, 536870912, 1073741824, 2147483648, 68719476736, 137438953472, 1099511627776, 2199023255552, 274877906944, 549755813888, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 281474976710656, 562949953421312, 70368744177664, 140737488355328, 1125899906842624, 2251799813685248]
private lemma liftProduct0a : decode 52 (WordCertificates.generatorRows 0) *
    decode 52 (WordCertificates.generatorRows 1) = decode 52 liftFirst0 := by
  apply decode_mul
  decide +kernel
private lemma liftProduct0b : decode 52 liftFirst0 *
    decode 52 (WordCertificates.generatorRows 0) = decode 52 liftRows0 := by
  apply decode_mul
  decide +kernel
private lemma liftVal0 : (embedding (simpleLift 0 0)).val = decode 52 liftRows0 := by
  simp only [simpleLift, map_mul, Units.val_mul, positive_decode, negative_decode]
  change (decode 52 (WordCertificates.generatorRows 0) *
    decode 52 (WordCertificates.generatorRows 1)) *
    decode 52 (WordCertificates.generatorRows 0) = _
  rw [liftProduct0a, liftProduct0b]
private def liftFirst1 : Array ℕ := #[1, 8589934595, 4, 8, 16, 32, 64, 128, 1280, 2048, 256, 2560, 4096, 8192, 16384, 32768, 1114112, 2097152, 4456448, 8388608, 65536, 2228224, 262144, 8912896, 285212672, 536870912, 1140850688, 2147483648, 16777216, 570425344, 67108864, 2281701376, 4294967296, 25769803777, 8589934592, 34359738368, 68719476736, 412316860416, 137438953472, 549755813888, 1099511627776, 6597069766656, 2199023255552, 8796093022208, 17592186044416, 105553116266496, 35184372088832, 140737488355328, 281474976710656, 1688849860263936, 562949953421312, 2251799813685248]
private def liftRows1 : Array ℕ := #[1, 3, 4, 8, 16, 32, 64, 128, 1024, 2048, 256, 512, 4096, 8192, 16384, 32768, 1048576, 2097152, 4194304, 8388608, 65536, 131072, 262144, 524288, 268435456, 536870912, 1073741824, 2147483648, 16777216, 33554432, 67108864, 134217728, 4294967296, 17179869184, 8589934592, 34359738368, 68719476736, 274877906944, 137438953472, 549755813888, 1099511627776, 4398046511104, 2199023255552, 8796093022208, 17592186044416, 70368744177664, 35184372088832, 140737488355328, 281474976710656, 1125899906842624, 562949953421312, 2251799813685248]
private lemma liftProduct1a : decode 52 (WordCertificates.generatorRows 2) *
    decode 52 (WordCertificates.generatorRows 3) = decode 52 liftFirst1 := by
  apply decode_mul
  decide +kernel
private lemma liftProduct1b : decode 52 liftFirst1 *
    decode 52 (WordCertificates.generatorRows 2) = decode 52 liftRows1 := by
  apply decode_mul
  decide +kernel
private lemma liftVal1 : (embedding (simpleLift 0 1)).val = decode 52 liftRows1 := by
  simp only [simpleLift, map_mul, Units.val_mul, positive_decode, negative_decode]
  change (decode 52 (WordCertificates.generatorRows 2) *
    decode 52 (WordCertificates.generatorRows 3)) *
    decode 52 (WordCertificates.generatorRows 2) = _
  rw [liftProduct1a, liftProduct1b]
private def liftFirst2 : Array ℕ := #[1, 2, 1038, 8, 1048592, 4194336, 268435520, 1073741952, 4294967552, 17179869696, 3082, 1024, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 3145728, 1048576, 12582912, 4194304, 16777216, 33554432, 67108864, 134217728, 805306368, 268435456, 3221225472, 1073741824, 12884901888, 4294967296, 51539607552, 17179869184, 206158430208, 68719476736, 824633720832, 274877906944, 3298534883328, 1099511627776, 13194139533312, 4398046511104, 52776558133248, 17592186044416, 211106232532992, 70368744177664, 844424930131968, 281474976710656, 3377699720527872, 1125899906842624]
private def liftRows2 : Array ℕ := #[1, 2, 14, 8, 16, 32, 64, 128, 256, 512, 2048, 1024, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 2097152, 1048576, 8388608, 4194304, 16777216, 33554432, 67108864, 134217728, 536870912, 268435456, 2147483648, 1073741824, 8589934592, 4294967296, 34359738368, 17179869184, 137438953472, 68719476736, 549755813888, 274877906944, 2199023255552, 1099511627776, 8796093022208, 4398046511104, 35184372088832, 17592186044416, 140737488355328, 70368744177664, 562949953421312, 281474976710656, 2251799813685248, 1125899906842624]
private lemma liftProduct2a : decode 52 (WordCertificates.generatorRows 4) *
    decode 52 (WordCertificates.generatorRows 5) = decode 52 liftFirst2 := by
  apply decode_mul
  decide +kernel
private lemma liftProduct2b : decode 52 liftFirst2 *
    decode 52 (WordCertificates.generatorRows 4) = decode 52 liftRows2 := by
  apply decode_mul
  decide +kernel
private lemma liftVal2 : (embedding (simpleLift 0 2)).val = decode 52 liftRows2 := by
  simp only [simpleLift, map_mul, Units.val_mul, positive_decode, negative_decode]
  change (decode 52 (WordCertificates.generatorRows 4) *
    decode 52 (WordCertificates.generatorRows 5)) *
    decode 52 (WordCertificates.generatorRows 4) = _
  rw [liftProduct2a, liftProduct2b]
private def liftFirst3 : Array ℕ := #[1, 2, 4, 8796093022220, 68719476752, 2251799813685248, 549755813888, 281474976710784, 2199023255552, 70368744178176, 4398046511104, 35184372090880, 4096, 4294975488, 34359738368, 32768, 65536, 268566528, 2147483648, 524288, 1048576, 18874368, 134217728, 8388608, 2097152, 33554432, 67108864, 138412032, 131072, 536870912, 1073741824, 2147745792, 8192, 8589934592, 17179869184, 34359754752, 16, 137441050624, 274878038016, 549755813952, 1099511635968, 2199023255808, 4398046512128, 26388279066628, 8796093022208, 2048, 512, 140771848093696, 128, 562952100904960, 1125900041060352, 2251799813685280]
private def liftRows3 : Array ℕ := #[1, 2, 4, 12, 68719476736, 2251799813685248, 549755813888, 281474976710656, 2199023255552, 70368744177664, 4398046511104, 35184372088832, 4096, 4294967296, 34359738368, 32768, 65536, 268435456, 2147483648, 524288, 1048576, 16777216, 134217728, 8388608, 2097152, 33554432, 67108864, 4194304, 131072, 536870912, 1073741824, 262144, 8192, 8589934592, 17179869184, 16384, 16, 137438953472, 274877906944, 64, 1099511627776, 256, 1024, 17592186044416, 8796093022208, 2048, 512, 140737488355328, 128, 562949953421312, 1125899906842624, 32]
private lemma liftProduct3a : decode 52 (WordCertificates.generatorRows 6) *
    decode 52 (WordCertificates.generatorRows 7) = decode 52 liftFirst3 := by
  apply decode_mul
  decide +kernel
private lemma liftProduct3b : decode 52 liftFirst3 *
    decode 52 (WordCertificates.generatorRows 6) = decode 52 liftRows3 := by
  apply decode_mul
  decide +kernel
private lemma liftVal3 : (embedding (simpleLift 0 3)).val = decode 52 liftRows3 := by
  simp only [simpleLift, map_mul, Units.val_mul, positive_decode, negative_decode]
  change (decode 52 (WordCertificates.generatorRows 6) *
    decode 52 (WordCertificates.generatorRows 7)) *
    decode 52 (WordCertificates.generatorRows 6) = _
  rw [liftProduct3a, liftProduct3b]

private def positiveIndex : Fin 24 → Fin 48 := ![22, 30, 7, 40, 26, 31, 5, 41, 27, 10, 3, 42, 23, 14, 44, 43, 18, 45, 19, 46, 15, 47, 11, 1]
private def positiveRoot (i : Fin 24) : F4Chevalley.Root :=
  ReeF4.Cartan.FieldSeparation.TraceValues.root (positiveIndex i)
private def positiveRows0 : Array ℕ := rows21
private lemma simpleRoot0 : positiveRoot 0 = typeF4SimpleRootIndex 0 := by
  apply Subtype.ext
  ext k
  fin_cases k <;> norm_num [positiveRoot, positiveIndex,
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private lemma positiveVal0 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 0) 1)).val = decode 52 positiveRows0 := by
  rw [simpleRoot0, positive_decode]
  rfl
private def positiveRows1 : Array ℕ := rows23
private lemma simpleRoot1 : positiveRoot 1 = typeF4SimpleRootIndex 1 := by
  apply Subtype.ext
  ext k
  fin_cases k <;> norm_num [positiveRoot, positiveIndex,
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private lemma positiveVal1 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 1) 1)).val = decode 52 positiveRows1 := by
  rw [simpleRoot1, positive_decode]
  rfl
private def positiveRows2 : Array ℕ := rows3
private lemma simpleRoot2 : positiveRoot 2 = typeF4SimpleRootIndex 2 := by
  apply Subtype.ext
  ext k
  fin_cases k <;> norm_num [positiveRoot, positiveIndex,
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private lemma positiveVal2 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 2) 1)).val = decode 52 positiveRows2 := by
  rw [simpleRoot2, positive_decode]
  rfl
private def positiveRows3 : Array ℕ := rows13
private lemma simpleRoot3 : positiveRoot 3 = typeF4SimpleRootIndex 3 := by
  apply Subtype.ext
  ext k
  fin_cases k <;> norm_num [positiveRoot, positiveIndex,
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private lemma positiveVal3 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 3) 1)).val = decode 52 positiveRows3 := by
  rw [simpleRoot3, positive_decode]
  rfl
private def positiveRows4 : Array ℕ := #[536870913, 536870914, 4, 8, 16, 32, 64, 2176, 256, 512, 1088, 2048, 4096, 2105344, 16384, 8421376, 65536, 131072, 262144, 524288, 1052672, 2097152, 4210688, 8388608, 16777216, 33554432, 8657043456, 34493956096, 268435456, 536870912, 1610612739, 2147483648, 4311744512, 8589934592, 17213423616, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888, 1236950581248, 2199023255552, 4947802324992, 8796093022208, 17592186044416, 35184372088832, 70368744177664, 140737488355328, 316659348799488, 562949953421312, 1266637395197952, 2251799813685248]
private lemma reflectRoot4 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (positiveRoot 0) =
      positiveRoot 4 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 22) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 26
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst4 : Array ℕ := #[33554433, 33554435, 4, 8, 16, 32, 64, 640, 1024, 2048, 320, 512, 4096, 139264, 16384, 557056, 1048576, 2097152, 4194304, 8388608, 69632, 131072, 278528, 524288, 268435456, 536870912, 18253611008, 36507222016, 16777216, 33554432, 100663298, 134217728, 4563402752, 17179869184, 9126805504, 34359738368, 68719476736, 274877906944, 137438953472, 549755813888, 1374389534720, 4398046511104, 2748779069440, 8796093022208, 17592186044416, 70368744177664, 35184372088832, 140737488355328, 351843720888320, 1125899906842624, 703687441776640, 2251799813685248]
private lemma reflectionProduct4a : decode 52 liftRows1 * decode 52 positiveRows0 =
    decode 52 reflectionFirst4 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct4b : decode 52 reflectionFirst4 * decode 52 liftRows1 =
    decode 52 positiveRows4 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal4 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 4) 1)).val = decode 52 positiveRows4 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 1 (positiveRoot 0))
  rw [reflectRoot4, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal1, positiveVal0, reflectionProduct4a, reflectionProduct4b] at hh
  exact hh.symm
private def positiveRows5 : Array ℕ := rows12
private lemma reflectRoot5 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 1) =
      positiveRoot 5 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 30) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 31
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst5 : Array ℕ := #[1, 8589934594, 8589934606, 8, 16, 32, 64, 128, 256, 2560, 2048, 1280, 4096, 8192, 16384, 32768, 65536, 2228224, 262144, 8912896, 2097152, 1114112, 8388608, 4456448, 16777216, 570425344, 67108864, 2281701376, 536870912, 285212672, 2147483648, 1140850688, 8589934592, 4294967296, 34359738368, 25769803777, 137438953472, 68719476736, 549755813888, 412316860416, 2199023255552, 1099511627776, 8796093022208, 6597069766656, 35184372088832, 17592186044416, 140737488355328, 105553116266496, 562949953421312, 281474976710656, 2251799813685248, 1688849860263936]
private lemma reflectionProduct5a : decode 52 liftRows2 * decode 52 positiveRows1 =
    decode 52 reflectionFirst5 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct5b : decode 52 reflectionFirst5 * decode 52 liftRows2 =
    decode 52 positiveRows5 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal5 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 5) 1)).val = decode 52 positiveRows5 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 1))
  rw [reflectRoot5, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal1, reflectionProduct5a, reflectionProduct5b] at hh
  exact hh.symm
private def positiveRows6 : Array ℕ := rows2
private lemma reflectRoot6 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (positiveRoot 2) =
      positiveRoot 6 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 7) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 5
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst6 : Array ℕ := #[1, 3, 1028, 8, 1048592, 4194336, 268435520, 1073741952, 1024, 3082, 4294967552, 17179869696, 4096, 8192, 16384, 32768, 1048576, 3145728, 4194304, 12582912, 65536, 131072, 262144, 524288, 268435456, 805306368, 1073741824, 3221225472, 16777216, 33554432, 67108864, 134217728, 4294967296, 17179869184, 12884901888, 51539607552, 68719476736, 274877906944, 206158430208, 824633720832, 1099511627776, 4398046511104, 3298534883328, 13194139533312, 17592186044416, 70368744177664, 52776558133248, 211106232532992, 281474976710656, 1125899906842624, 844424930131968, 3377699720527872]
private lemma reflectionProduct6a : decode 52 liftRows1 * decode 52 positiveRows2 =
    decode 52 reflectionFirst6 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct6b : decode 52 reflectionFirst6 * decode 52 liftRows1 =
    decode 52 positiveRows6 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal6 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 6) 1)).val = decode 52 positiveRows6 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 1 (positiveRoot 2))
  rw [reflectRoot6, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal1, positiveVal2, reflectionProduct6a, reflectionProduct6b] at hh
  exact hh.symm
private def positiveRows7 : Array ℕ := rows14
private lemma reflectRoot7 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 2) =
      positiveRoot 7 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 7) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 41
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst7 : Array ℕ := #[1, 2, 1028, 1036, 68719476736, 3377699720527872, 824633720832, 281474976710656, 3298534883328, 70368744177664, 4398046511104, 52776558133248, 4096, 4294967296, 51539607552, 32768, 65536, 268435456, 3221225472, 524288, 1048576, 16777216, 134217728, 12582912, 3145728, 33554432, 67108864, 4194304, 131072, 805306368, 1073741824, 262144, 8192, 12884901888, 17179869184, 16384, 1048592, 206158430208, 274877906944, 268435520, 1099511627776, 4294967552, 1024, 17592186044416, 13194139533312, 3082, 17179869696, 211106232532992, 1073741952, 844424930131968, 1125899906842624, 4194336]
private lemma reflectionProduct7a : decode 52 liftRows3 * decode 52 positiveRows2 =
    decode 52 reflectionFirst7 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct7b : decode 52 reflectionFirst7 * decode 52 liftRows3 =
    decode 52 positiveRows7 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal7 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 7) 1)).val = decode 52 positiveRows7 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 2))
  rw [reflectRoot7, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal2, reflectionProduct7a, reflectionProduct7b] at hh
  exact hh.symm
private def positiveRows8 : Array ℕ := rows11
private lemma reflectRoot8 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 4) =
      positiveRoot 8 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 26) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 27
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst8 : Array ℕ := #[536870913, 536870914, 536870926, 8, 16, 32, 64, 2176, 256, 512, 2048, 1088, 4096, 2105344, 16384, 8421376, 65536, 131072, 262144, 524288, 2097152, 1052672, 8388608, 4210688, 16777216, 33554432, 8657043456, 34493956096, 536870912, 268435456, 2147483648, 1610612739, 8589934592, 4311744512, 34359738368, 17213423616, 137438953472, 68719476736, 549755813888, 274877906944, 2199023255552, 1236950581248, 8796093022208, 4947802324992, 35184372088832, 17592186044416, 140737488355328, 70368744177664, 562949953421312, 316659348799488, 2251799813685248, 1266637395197952]
private lemma reflectionProduct8a : decode 52 liftRows2 * decode 52 positiveRows4 =
    decode 52 reflectionFirst8 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct8b : decode 52 reflectionFirst8 * decode 52 liftRows2 =
    decode 52 positiveRows8 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal8 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 8) 1)).val = decode 52 positiveRows8 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 4))
  rw [reflectRoot8, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal4, reflectionProduct8a, reflectionProduct8b] at hh
  exact hh.symm
private def positiveRows9 : Array ℕ := rows4
private lemma reflectRoot9 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 5) =
      positiveRoot 9 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 31) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 10
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst9 : Array ℕ := #[1, 4294967298, 4294967300, 4294967308, 68719476736, 2533274790395904, 618475290624, 281474976710656, 2199023255552, 70368744177664, 4398046511104, 35184372088832, 4096, 4294967296, 38654705665, 32768, 65536, 268435456, 2214592512, 4718592, 1048576, 16777216, 1207959552, 8650752, 2162688, 301989888, 67108864, 4194304, 1179648, 553648128, 1073741824, 262144, 8192, 8589934592, 17179869184, 16384, 16, 137438953472, 274877906944, 64, 1099511627776, 256, 1024, 17592186044416, 9895604649984, 2304, 1536, 158329674399744, 128, 562949953421312, 1125899906842624, 32]
private lemma reflectionProduct9a : decode 52 liftRows3 * decode 52 positiveRows5 =
    decode 52 reflectionFirst9 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct9b : decode 52 reflectionFirst9 * decode 52 liftRows3 =
    decode 52 positiveRows9 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal9 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 9) 1)).val = decode 52 positiveRows9 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 5))
  rw [reflectRoot9, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal5, reflectionProduct9a, reflectionProduct9b] at hh
  exact hh.symm
private def positiveRows10 : Array ℕ := rows1
private lemma reflectRoot10 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (positiveRoot 6) =
      positiveRoot 10 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 5) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 3
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst10 : Array ℕ := #[3, 2, 260, 8, 65552, 262176, 256, 779, 16777280, 67108992, 4294968320, 8589936640, 65536, 196608, 262144, 786432, 4096, 8192, 16384, 32768, 1048576, 2097152, 4194304, 8388608, 16777216, 67108864, 50331648, 201326592, 4294967296, 8589934592, 21474836480, 42949672960, 268435456, 536870912, 1073741824, 2147483648, 68719476736, 137438953472, 1099511627776, 2199023255552, 343597383680, 687194767360, 5497558138880, 10995116277760, 17592186044416, 35184372088832, 281474976710656, 562949953421312, 87960930222080, 175921860444160, 1407374883553280, 2814749767106560]
private lemma reflectionProduct10a : decode 52 liftRows0 * decode 52 positiveRows6 =
    decode 52 reflectionFirst10 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct10b : decode 52 reflectionFirst10 * decode 52 liftRows0 =
    decode 52 positiveRows10 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal10 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 10) 1)).val = decode 52 positiveRows10 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 0 (positiveRoot 6))
  rw [reflectRoot10, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal0, positiveVal6, reflectionProduct10a, reflectionProduct10b] at hh
  exact hh.symm
private def positiveRows11 : Array ℕ := rows15
private lemma reflectRoot11 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 6) =
      positiveRoot 11 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 5) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 42
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst11 : Array ℕ := #[1, 2, 260, 268, 68719476736, 2814749767106560, 687194767360, 281474976710656, 2199023255552, 87960930222080, 5497558138880, 35184372088832, 4096, 4294967296, 42949672960, 32768, 65536, 268435456, 2147483648, 786432, 1048576, 16777216, 201326592, 8388608, 2097152, 50331648, 67108864, 4194304, 196608, 536870912, 1073741824, 262144, 8192, 8589934592, 21474836480, 16384, 65552, 137438953472, 343597383680, 16777280, 1099511627776, 256, 4294968320, 17592186044416, 10995116277760, 8589936640, 779, 175921860444160, 67108992, 562949953421312, 1407374883553280, 262176]
private lemma reflectionProduct11a : decode 52 liftRows3 * decode 52 positiveRows6 =
    decode 52 reflectionFirst11 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct11b : decode 52 reflectionFirst11 * decode 52 liftRows3 =
    decode 52 positiveRows11 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal11 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 11) 1)).val = decode 52 positiveRows11 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 6))
  rw [reflectRoot11, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal6, reflectionProduct11a, reflectionProduct11b] at hh
  exact hh.symm
private def positiveRows12 : Array ℕ := rows10
private lemma reflectRoot12 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (positiveRoot 8) =
      positiveRoot 12 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 27) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 23
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst12 : Array ℕ := #[268435457, 3, 268435460, 8, 16, 32, 64, 1152, 1024, 2112, 256, 512, 4096, 1056768, 16384, 4227072, 1048576, 2101248, 4194304, 8404992, 65536, 131072, 262144, 524288, 268435456, 536870912, 1073741824, 2415919107, 16777216, 33554432, 4362076160, 17314086912, 4294967296, 17179869184, 8606711808, 34393292800, 68719476736, 274877906944, 137438953472, 549755813888, 1099511627776, 4398046511104, 2267742732288, 9070970929152, 17592186044416, 70368744177664, 35184372088832, 140737488355328, 281474976710656, 1125899906842624, 580542139465728, 2322168557862912]
private lemma reflectionProduct12a : decode 52 liftRows1 * decode 52 positiveRows8 =
    decode 52 reflectionFirst12 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct12b : decode 52 reflectionFirst12 * decode 52 liftRows1 =
    decode 52 positiveRows12 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal12 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 12) 1)).val = decode 52 positiveRows12 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 1 (positiveRoot 8))
  rw [reflectRoot12, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal1, positiveVal8, reflectionProduct12a, reflectionProduct12b] at hh
  exact hh.symm
private def positiveRows13 : Array ℕ := rows6
private lemma reflectRoot13 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 8) =
      positiveRoot 13 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 27) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 14
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst13 : Array ℕ := #[268435457, 268435458, 268435460, 268435468, 68719476736, 2322168557862912, 549755813888, 281474976710656, 2267742732288, 70368744177664, 4398046511104, 35184372088832, 4096, 4294967296, 34393292800, 4227072, 65536, 268435456, 2415919107, 524288, 1048576, 16777216, 17314086912, 8404992, 2101248, 33554432, 4362076160, 4194304, 131072, 536870912, 1073741824, 262144, 1056768, 8606711808, 17179869184, 16384, 16, 137438953472, 274877906944, 64, 1099511627776, 256, 1024, 17592186044416, 9070970929152, 2112, 512, 140737488355328, 1152, 580542139465728, 1125899906842624, 32]
private lemma reflectionProduct13a : decode 52 liftRows3 * decode 52 positiveRows8 =
    decode 52 reflectionFirst13 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct13b : decode 52 reflectionFirst13 * decode 52 liftRows3 =
    decode 52 positiveRows13 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal13 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 13) 1)).val = decode 52 positiveRows13 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 8))
  rw [reflectRoot13, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal8, reflectionProduct13a, reflectionProduct13b] at hh
  exact hh.symm
private def positiveRows14 : Array ℕ := rows17
private lemma reflectRoot14 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 10) =
      positiveRoot 14 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 3) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 44
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst14 : Array ℕ := #[1, 2, 68, 76, 68719476736, 2392537302040576, 549755813888, 299067162755072, 2336462209024, 70368744177664, 4672924418048, 35184372088832, 4096, 4294967296, 34359738368, 49152, 65536, 268435456, 2684354560, 524288, 1048576, 16777216, 167772160, 8388608, 2097152, 33554432, 83886080, 4194304, 131072, 536870912, 1342177280, 262144, 12288, 8589934592, 17179869184, 16384, 4112, 137438953472, 274877906944, 64, 1168231104512, 16777472, 268436480, 17592186044416, 9345848836096, 536872960, 33554944, 140737488355328, 201, 598134325510144, 1196268651020288, 16416]
private lemma reflectionProduct14a : decode 52 liftRows3 * decode 52 positiveRows10 =
    decode 52 reflectionFirst14 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct14b : decode 52 reflectionFirst14 * decode 52 liftRows3 =
    decode 52 positiveRows14 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal14 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 14) 1)).val = decode 52 positiveRows14 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 10))
  rw [reflectRoot14, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal10, reflectionProduct14a, reflectionProduct14b] at hh
  exact hh.symm
private def positiveRows15 : Array ℕ := rows16
private lemma reflectRoot15 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 11) =
      positiveRoot 15 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 42) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 43
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst15 : Array ℕ := #[1, 2, 14, 2199023255560, 16, 562949953421344, 137438953536, 128, 256, 8796093022720, 2048, 1099511628800, 4096, 8192, 8589950976, 32768, 65536, 131072, 262144, 2148007936, 2097152, 1048576, 8388608, 71303168, 16777216, 35651584, 67108864, 134217728, 536870912, 268500992, 2147483648, 1073741824, 8589934592, 4294967296, 34359738368, 17179877376, 137438953472, 68719542272, 549757911040, 274877906960, 2199023255552, 1099511627776, 8796093022208, 4398046519296, 35192962023424, 17592186044672, 140737488357376, 72567767433231, 562949953421312, 281475043819520, 2251801961168896, 1125899906842752]
private lemma reflectionProduct15a : decode 52 liftRows2 * decode 52 positiveRows11 =
    decode 52 reflectionFirst15 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct15b : decode 52 reflectionFirst15 * decode 52 liftRows2 =
    decode 52 positiveRows15 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal15 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 15) 1)).val = decode 52 positiveRows15 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 11))
  rw [reflectRoot15, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal11, reflectionProduct15a, reflectionProduct15b] at hh
  exact hh.symm
private def positiveRows16 : Array ℕ := rows8
private lemma reflectRoot16 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 12) =
      positiveRoot 16 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 23) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 18
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst16 : Array ℕ := #[16777217, 2, 16777220, 16777228, 68719476736, 2286984185774080, 549755813888, 281474976710656, 2199023255552, 70368744177664, 4466765987840, 35184372088832, 4096, 4294967296, 34896609280, 294912, 65536, 268435456, 10737418240, 540672, 1048576, 16777216, 150994946, 8388608, 2097152, 33554432, 67108864, 4194304, 135168, 536870912, 5368709120, 262144, 73728, 8589934592, 17448304640, 16384, 16, 137438953472, 274877906944, 64, 1099511627776, 256, 1024, 17592186044416, 8933531975680, 2048, 576, 140737488355328, 384, 562949953421312, 1143492092887040, 32]
private lemma reflectionProduct16a : decode 52 liftRows3 * decode 52 positiveRows12 =
    decode 52 reflectionFirst16 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct16b : decode 52 reflectionFirst16 * decode 52 liftRows3 =
    decode 52 positiveRows16 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal16 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 16) 1)).val = decode 52 positiveRows16 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 12))
  rw [reflectRoot16, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal12, reflectionProduct16a, reflectionProduct16b] at hh
  exact hh.symm
private def positiveRows17 : Array ℕ := rows18
private lemma reflectRoot17 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 14) =
      positiveRoot 17 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 44) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 45
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst17 : Array ℕ := #[1, 2, 14, 549755813896, 16, 140737488355360, 64, 8796093022336, 137438953728, 512, 2048, 274877907968, 4096, 8192, 16384, 34359771136, 65536, 131072, 537133056, 524288, 2097152, 1048576, 8388608, 37748736, 16777216, 33554432, 69206016, 134217728, 536870912, 268435456, 2147483648, 1073872896, 8589934592, 4294971392, 34359738368, 17179869184, 137438953472, 68719480832, 549755813888, 274877906944, 2199025352704, 1099511627792, 8796093022208, 4398046642176, 35184908959744, 17592186044480, 140737488355328, 70368777732096, 562949953423360, 282024732524557, 2251834173423616, 1125899906843136]
private lemma reflectionProduct17a : decode 52 liftRows2 * decode 52 positiveRows14 =
    decode 52 reflectionFirst17 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct17b : decode 52 reflectionFirst17 * decode 52 liftRows2 =
    decode 52 positiveRows17 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal17 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 17) 1)).val = decode 52 positiveRows17 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 14))
  rw [reflectRoot17, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal14, reflectionProduct17a, reflectionProduct17b] at hh
  exact hh.symm
private def positiveRows18 : Array ℕ := rows9
private lemma reflectRoot18 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 16) =
      positiveRoot 18 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 18) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 19
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst18 : Array ℕ := #[2097153, 2, 14, 2097160, 16, 2080, 64, 128, 256, 512, 2048, 1040, 4096, 8192, 536887296, 2147516416, 65536, 131072, 8590196736, 34360262656, 2097152, 1048576, 8388608, 6291458, 16777216, 33554432, 67108864, 134217728, 536870912, 268439552, 2147483648, 1073750016, 8589934592, 4295032832, 34359738368, 17180000256, 137438953472, 68719476736, 549755813888, 274877906944, 2199023255552, 1099511627776, 8796093022208, 4398046511104, 35184372088832, 17729624997888, 140737488355328, 70918499991552, 562949953421312, 283673999966208, 2251799813685248, 1134695999864832]
private lemma reflectionProduct18a : decode 52 liftRows2 * decode 52 positiveRows16 =
    decode 52 reflectionFirst18 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct18b : decode 52 reflectionFirst18 * decode 52 liftRows2 =
    decode 52 positiveRows18 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal18 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 18) 1)).val = decode 52 positiveRows18 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 16))
  rw [reflectRoot18, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal16, reflectionProduct18a, reflectionProduct18b] at hh
  exact hh.symm
private def positiveRows19 : Array ℕ := rows19
private lemma reflectRoot19 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (positiveRoot 17) =
      positiveRoot 19 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 45) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 46
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst19 : Array ℕ := #[1, 3, 4, 274877906952, 16, 70368744177696, 64, 4398046511232, 1024, 549755815936, 68719476992, 512, 4096, 8192, 16384, 17179901952, 1048576, 2097152, 4194304, 41943040, 65536, 131072, 268697600, 524288, 268435456, 536870912, 1073741824, 2147614720, 16777216, 33554432, 68157440, 134217728, 4294967296, 17179869184, 8589938688, 34359738368, 68719476736, 274877906944, 137438957568, 549755813888, 1099512676352, 4398046511104, 2199023255568, 8796093153280, 17592454479872, 70368744177664, 35184372088896, 140737521909760, 281474976711680, 1125917086711808, 563224831328263, 2251799813685760]
private lemma reflectionProduct19a : decode 52 liftRows1 * decode 52 positiveRows17 =
    decode 52 reflectionFirst19 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct19b : decode 52 reflectionFirst19 * decode 52 liftRows1 =
    decode 52 positiveRows19 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal19 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 19) 1)).val = decode 52 positiveRows19 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 1 (positiveRoot 17))
  rw [reflectRoot19, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal1, positiveVal17, reflectionProduct19a, reflectionProduct19b] at hh
  exact hh.symm
private def positiveRows20 : Array ℕ := rows7
private lemma reflectRoot20 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (positiveRoot 18) =
      positiveRoot 20 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 19) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 15
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst20 : Array ℕ := #[1048577, 1048579, 4, 1048584, 16, 1056, 64, 128, 1024, 2064, 256, 512, 4096, 8192, 268451840, 1073774592, 1048576, 2097152, 4194304, 9437186, 65536, 131072, 4295229440, 17180393472, 268435456, 536875008, 1073741824, 2147491840, 16777216, 33554432, 67108864, 134217728, 4294967296, 17179869184, 8590000128, 34359869440, 68719476736, 274877906944, 137438953472, 549755813888, 1099511627776, 4398046511104, 2199023255552, 8796093022208, 17592186044416, 70368744177664, 35253091565568, 141012366262272, 281474976710656, 1125899906842624, 564049465049088, 2256197860196352]
private lemma reflectionProduct20a : decode 52 liftRows1 * decode 52 positiveRows18 =
    decode 52 reflectionFirst20 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct20b : decode 52 reflectionFirst20 * decode 52 liftRows1 =
    decode 52 positiveRows20 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal20 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 20) 1)).val = decode 52 positiveRows20 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 1 (positiveRoot 18))
  rw [reflectRoot20, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal1, positiveVal18, reflectionProduct20a, reflectionProduct20b] at hh
  exact hh.symm
private def positiveRows21 : Array ℕ := rows20
private lemma reflectRoot21 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (positiveRoot 19) =
      positiveRoot 21 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 46) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 47
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst21 : Array ℕ := #[1, 2, 137438953486, 137438953480, 16, 35184372088864, 64, 2199023255680, 256, 549755814400, 2048, 68719477760, 4096, 8192, 16384, 8589967360, 65536, 131072, 262144, 537395200, 2097152, 1048576, 8388608, 20971520, 16777216, 33554432, 67108864, 136314880, 536870912, 268435456, 2147483648, 1073807360, 8589934592, 4294967296, 34359738368, 17179873280, 137438953472, 68719476736, 549755813888, 274877911040, 2199023255552, 1099511693312, 8796095119360, 4398046511120, 35184372088832, 17592202821632, 140738025226240, 70368744177728, 562958543355904, 281474976710912, 2251799813687296, 1126037345796102]
private lemma reflectionProduct21a : decode 52 liftRows2 * decode 52 positiveRows19 =
    decode 52 reflectionFirst21 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct21b : decode 52 reflectionFirst21 * decode 52 liftRows2 =
    decode 52 positiveRows21 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal21 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 21) 1)).val = decode 52 positiveRows21 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 2 (positiveRoot 19))
  rw [reflectRoot21, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal2, positiveVal19, reflectionProduct21a, reflectionProduct21b] at hh
  exact hh.symm
private def positiveRows22 : Array ℕ := rows5
private lemma reflectRoot22 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (positiveRoot 20) =
      positiveRoot 22 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 15) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 11
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst22 : Array ℕ := #[3, 65538, 4, 65544, 16, 288, 256, 528, 64, 128, 1024, 2048, 65536, 131072, 262144, 589827, 4096, 8192, 16793600, 67141632, 1048576, 2097152, 4299161600, 8598323200, 16777216, 67108864, 33558528, 134225920, 4294967296, 8589934592, 17180917760, 34361835520, 268435456, 536870912, 1073741824, 2147483648, 68719476736, 137438953472, 1099511627776, 2199023255552, 274877906944, 549755813888, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 281474976710656, 562949953421312, 70437463654400, 140874927308800, 1126999418470400, 2253998836940800]
private lemma reflectionProduct22a : decode 52 liftRows0 * decode 52 positiveRows20 =
    decode 52 reflectionFirst22 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct22b : decode 52 reflectionFirst22 * decode 52 liftRows0 =
    decode 52 positiveRows22 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal22 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 22) 1)).val = decode 52 positiveRows22 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 0 (positiveRoot 20))
  rw [reflectRoot22, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal0, positiveVal20, reflectionProduct22a, reflectionProduct22b] at hh
  exact hh.symm
private def positiveRows23 : Array ℕ := rows0
private lemma reflectRoot23 :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) (positiveRoot 21) =
      positiveRoot 23 := by
  change typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
    (ReeF4.Cartan.FieldSeparation.TraceValues.root 47) =
      ReeF4.Cartan.FieldSeparation.TraceValues.root 1
  apply Subtype.ext
  rw [simple_reflection_val]
  ext k
  fin_cases k <;> norm_num [
    ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three]
private def reflectionFirst23 : Array ℕ := #[1, 2, 68719476740, 12, 68719476736, 2251868533161996, 549755817984, 281479271677952, 2199023321088, 70369012613120, 4398047559680, 35184388866048, 4096, 4294967296, 34359742464, 4295000064, 65536, 268435456, 2147549184, 268959744, 1048576, 16777216, 135266304, 25165824, 2097152, 33554432, 67108864, 4194304, 131072, 536870912, 1073741824, 262144, 8192, 8589934592, 17179869184, 16384, 16, 137438953472, 274877906944, 64, 1099511627776, 256, 1024, 17592186044416, 8796093022224, 137438955520, 274877907456, 140737488355392, 1099511627904, 562949953421568, 1125899906843648, 17592186044448]
private lemma reflectionProduct23a : decode 52 liftRows3 * decode 52 positiveRows21 =
    decode 52 reflectionFirst23 := by
  apply decode_mul
  decide +kernel
private lemma reflectionProduct23b : decode 52 reflectionFirst23 * decode 52 liftRows3 =
    decode 52 positiveRows23 := by
  apply decode_mul
  decide +kernel
private lemma positiveVal23 :
    (embedding (rootGeneratorInGroup 0 (positiveRoot 23) 1)).val = decode 52 positiveRows23 := by
  have hh := congrArg (fun x => (embedding x).val) (simple_conjugation 3 (positiveRoot 21))
  rw [reflectRoot23, lift_inverse] at hh
  simp only [map_mul, Units.val_mul] at hh
  rw [liftVal3, positiveVal21, reflectionProduct23a, reflectionProduct23b] at hh
  exact hh.symm
private lemma positivePos0 : typeF4RootPairing_base.IsPos (positiveRoot 0) := by
  rw [simpleRoot0]
  exact typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 0).property
private lemma positivePos1 : typeF4RootPairing_base.IsPos (positiveRoot 1) := by
  rw [simpleRoot1]
  exact typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 1).property
private lemma positivePos2 : typeF4RootPairing_base.IsPos (positiveRoot 2) := by
  rw [simpleRoot2]
  exact typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 2).property
private lemma positivePos3 : typeF4RootPairing_base.IsPos (positiveRoot 3) := by
  rw [simpleRoot3]
  exact typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv 3).property
private lemma positivePos4 : typeF4RootPairing_base.IsPos (positiveRoot 4) := by
  rw [← reflectRoot4]
  apply positivePos0.reflectionPerm (typeF4RootPairing_baseEquiv 1).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 22 = typeF4SimpleRootIndex 1 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 1) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos5 : typeF4RootPairing_base.IsPos (positiveRoot 5) := by
  rw [← reflectRoot5]
  apply positivePos1.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 30 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 2) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos6 : typeF4RootPairing_base.IsPos (positiveRoot 6) := by
  rw [← reflectRoot6]
  apply positivePos2.reflectionPerm (typeF4RootPairing_baseEquiv 1).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 7 = typeF4SimpleRootIndex 1 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 2) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos7 : typeF4RootPairing_base.IsPos (positiveRoot 7) := by
  rw [← reflectRoot7]
  apply positivePos2.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 7 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos8 : typeF4RootPairing_base.IsPos (positiveRoot 8) := by
  rw [← reflectRoot8]
  apply positivePos4.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 26 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 1) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos9 : typeF4RootPairing_base.IsPos (positiveRoot 9) := by
  rw [← reflectRoot9]
  apply positivePos5.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 31 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos10 : typeF4RootPairing_base.IsPos (positiveRoot 10) := by
  rw [← reflectRoot10]
  apply positivePos6.reflectionPerm (typeF4RootPairing_baseEquiv 0).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 5 = typeF4SimpleRootIndex 0 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 1) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos11 : typeF4RootPairing_base.IsPos (positiveRoot 11) := by
  rw [← reflectRoot11]
  apply positivePos6.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 5 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos12 : typeF4RootPairing_base.IsPos (positiveRoot 12) := by
  rw [← reflectRoot12]
  apply positivePos8.reflectionPerm (typeF4RootPairing_baseEquiv 1).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 27 = typeF4SimpleRootIndex 1 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 1) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos13 : typeF4RootPairing_base.IsPos (positiveRoot 13) := by
  rw [← reflectRoot13]
  apply positivePos8.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 27 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos14 : typeF4RootPairing_base.IsPos (positiveRoot 14) := by
  rw [← reflectRoot14]
  apply positivePos10.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 3 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos15 : typeF4RootPairing_base.IsPos (positiveRoot 15) := by
  rw [← reflectRoot15]
  apply positivePos11.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 42 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos16 : typeF4RootPairing_base.IsPos (positiveRoot 16) := by
  rw [← reflectRoot16]
  apply positivePos12.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 23 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos17 : typeF4RootPairing_base.IsPos (positiveRoot 17) := by
  rw [← reflectRoot17]
  apply positivePos14.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 44 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos18 : typeF4RootPairing_base.IsPos (positiveRoot 18) := by
  rw [← reflectRoot18]
  apply positivePos16.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 18 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos19 : typeF4RootPairing_base.IsPos (positiveRoot 19) := by
  rw [← reflectRoot19]
  apply positivePos17.reflectionPerm (typeF4RootPairing_baseEquiv 1).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 45 = typeF4SimpleRootIndex 1 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos20 : typeF4RootPairing_base.IsPos (positiveRoot 20) := by
  rw [← reflectRoot20]
  apply positivePos18.reflectionPerm (typeF4RootPairing_baseEquiv 1).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 19 = typeF4SimpleRootIndex 1 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos21 : typeF4RootPairing_base.IsPos (positiveRoot 21) := by
  rw [← reflectRoot21]
  apply positivePos19.reflectionPerm (typeF4RootPairing_baseEquiv 2).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 46 = typeF4SimpleRootIndex 2 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos22 : typeF4RootPairing_base.IsPos (positiveRoot 22) := by
  rw [← reflectRoot22]
  apply positivePos20.reflectionPerm (typeF4RootPairing_baseEquiv 0).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 15 = typeF4SimpleRootIndex 0 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 0) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma positivePos23 : typeF4RootPairing_base.IsPos (positiveRoot 23) := by
  rw [← reflectRoot23]
  apply positivePos21.reflectionPerm (typeF4RootPairing_baseEquiv 3).property
  intro hh
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 47 = typeF4SimpleRootIndex 3 at hh
  have hv := congrArg (fun r : F4Chevalley.Root => r.val 1) hh
  norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    typeF4SimpleRootIndex, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at hv
private lemma negative_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]
private lemma negativeRoot0 : ReeF4.Cartan.FieldSeparation.TraceValues.root 0 = -(positiveRoot 23) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 0 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 1)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot2 : ReeF4.Cartan.FieldSeparation.TraceValues.root 2 = -(positiveRoot 10) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 2 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 3)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot4 : ReeF4.Cartan.FieldSeparation.TraceValues.root 4 = -(positiveRoot 6) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 4 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 5)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot6 : ReeF4.Cartan.FieldSeparation.TraceValues.root 6 = -(positiveRoot 2) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 6 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 7)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot8 : ReeF4.Cartan.FieldSeparation.TraceValues.root 8 = -(positiveRoot 22) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 8 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 11)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot9 : ReeF4.Cartan.FieldSeparation.TraceValues.root 9 = -(positiveRoot 9) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 9 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 10)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot12 : ReeF4.Cartan.FieldSeparation.TraceValues.root 12 = -(positiveRoot 20) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 12 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 15)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot13 : ReeF4.Cartan.FieldSeparation.TraceValues.root 13 = -(positiveRoot 13) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 13 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 14)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot16 : ReeF4.Cartan.FieldSeparation.TraceValues.root 16 = -(positiveRoot 18) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 16 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 19)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot17 : ReeF4.Cartan.FieldSeparation.TraceValues.root 17 = -(positiveRoot 16) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 17 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 18)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot20 : ReeF4.Cartan.FieldSeparation.TraceValues.root 20 = -(positiveRoot 12) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 20 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 23)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot21 : ReeF4.Cartan.FieldSeparation.TraceValues.root 21 = -(positiveRoot 0) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 21 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 22)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot24 : ReeF4.Cartan.FieldSeparation.TraceValues.root 24 = -(positiveRoot 8) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 24 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 27)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot25 : ReeF4.Cartan.FieldSeparation.TraceValues.root 25 = -(positiveRoot 4) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 25 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 26)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot28 : ReeF4.Cartan.FieldSeparation.TraceValues.root 28 = -(positiveRoot 5) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 28 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 31)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot29 : ReeF4.Cartan.FieldSeparation.TraceValues.root 29 = -(positiveRoot 1) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 29 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 30)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot32 : ReeF4.Cartan.FieldSeparation.TraceValues.root 32 = -(positiveRoot 21) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 32 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 47)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot33 : ReeF4.Cartan.FieldSeparation.TraceValues.root 33 = -(positiveRoot 19) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 33 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 46)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot34 : ReeF4.Cartan.FieldSeparation.TraceValues.root 34 = -(positiveRoot 17) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 34 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 45)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot35 : ReeF4.Cartan.FieldSeparation.TraceValues.root 35 = -(positiveRoot 14) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 35 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 44)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot36 : ReeF4.Cartan.FieldSeparation.TraceValues.root 36 = -(positiveRoot 15) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 36 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 43)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot37 : ReeF4.Cartan.FieldSeparation.TraceValues.root 37 = -(positiveRoot 11) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 37 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 42)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot38 : ReeF4.Cartan.FieldSeparation.TraceValues.root 38 = -(positiveRoot 7) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 38 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 41)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]
private lemma negativeRoot39 : ReeF4.Cartan.FieldSeparation.TraceValues.root 39 = -(positiveRoot 3) := by
  change ReeF4.Cartan.FieldSeparation.TraceValues.root 39 =
    -(ReeF4.Cartan.FieldSeparation.TraceValues.root 40)
  apply Subtype.ext
  rw [negative_val]
  ext k
  fin_cases k <;> norm_num [ReeF4.Cartan.FieldSeparation.TraceValues.root, realCoord, coord,
    Matrix.cons_val_two, Matrix.cons_val_three]

private lemma positive_exhaustive (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
    ∃ i, r = positiveRoot i := by
  obtain ⟨i,rfl⟩ := root_surjective r
  fin_cases i
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot0 ▸ hr) positivePos23).elim
  · exact ⟨23, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot2 ▸ hr) positivePos10).elim
  · exact ⟨10, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot4 ▸ hr) positivePos6).elim
  · exact ⟨6, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot6 ▸ hr) positivePos2).elim
  · exact ⟨2, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot8 ▸ hr) positivePos22).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot9 ▸ hr) positivePos9).elim
  · exact ⟨9, rfl⟩
  · exact ⟨22, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot12 ▸ hr) positivePos20).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot13 ▸ hr) positivePos13).elim
  · exact ⟨13, rfl⟩
  · exact ⟨20, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot16 ▸ hr) positivePos18).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot17 ▸ hr) positivePos16).elim
  · exact ⟨16, rfl⟩
  · exact ⟨18, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot20 ▸ hr) positivePos12).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot21 ▸ hr) positivePos0).elim
  · exact ⟨0, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot24 ▸ hr) positivePos8).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot25 ▸ hr) positivePos4).elim
  · exact ⟨4, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot28 ▸ hr) positivePos5).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot29 ▸ hr) positivePos1).elim
  · exact ⟨1, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot32 ▸ hr) positivePos21).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot33 ▸ hr) positivePos19).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot34 ▸ hr) positivePos17).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot35 ▸ hr) positivePos14).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot36 ▸ hr) positivePos15).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot37 ▸ hr) positivePos11).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot38 ▸ hr) positivePos7).elim
  · exact ((RootPairing.Base.IsPos.neg_iff_not _ _).mp (negativeRoot39 ▸ hr) positivePos3).elim
  · exact ⟨3, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨17, rfl⟩
  · exact ⟨19, rfl⟩
  · exact ⟨21, rfl⟩
open ReeF4.LargeLocalSeeds

/-- The canonical positive subgroup in the original binary coordinates. -/
def U : Subgroup Matˣ := (splitUnipotent 0).map embedding

theorem U_isPGroup : IsPGroup 2 U := (splitUnipotent_isPGroup 0).map embedding

private lemma positive_long (i : Fin 2) :
    embedding (rootGeneratorInGroup 0 (typeF4SimpleRootIndex i.castSucc.castSucc) 1) =
      levi ⟨2*i.val, by omega⟩ := by
  apply Units.ext
  rw [positive_decode]
  fin_cases i <;> rfl

private lemma negative_long (i : Fin 2) :
    embedding (rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i.castSucc.castSucc) 1) =
      levi ⟨2*i.val+1, by omega⟩ := by
  apply Units.ext
  rw [negative_decode]
  fin_cases i <;> rfl

private lemma positive_long_mem (i : Fin 2) :
    embedding (rootGeneratorInGroup 0 (typeF4SimpleRootIndex i.castSucc.castSucc) 1) ∈ A := by
  rw [positive_long]
  exact levi_mem _

private lemma negative_long_mem (i : Fin 2) :
    embedding (rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i.castSucc.castSucc) 1) ∈ A := by
  rw [negative_long]
  exact levi_mem _

private lemma fourth_mem : embedding (rootGeneratorInGroup 0 (positiveRoot 4) 1) ∈ A := by
  have hh := congrArg embedding (simple_conjugation 1 (positiveRoot 0))
  rw [reflectRoot4, simpleRoot0] at hh
  rw [← hh, map_mul, map_mul, map_inv]
  have hl : embedding (simpleLift 0 1) ∈ A := by
    change embedding (rootGeneratorInGroup 0 (typeF4SimpleRootIndex 1) 1 *
      rootGeneratorInGroup 0 (-typeF4SimpleRootIndex 1) 1 *
      rootGeneratorInGroup 0 (typeF4SimpleRootIndex 1) 1) ∈ A
    rw [map_mul,map_mul]
    exact A.mul_mem (A.mul_mem (positive_long_mem 1) (negative_long_mem 1)) (positive_long_mem 1)
  exact A.mul_mem (A.mul_mem hl (positive_long_mem 0)) (A.inv_mem hl)

private lemma parameter_zero (r : F4Chevalley.Root) : rootGeneratorInGroup 0 r 0 = 1 := by
  apply Subtype.ext
  exact F4Chevalley.rootCurve_zero r

private lemma parameter_cases (t : CoefficientField 0) : t = 0 ∨ t = 1 := by
  apply eq_zero_or_one_of_sq_eq_self
  simpa using field_pow 0 t

private lemma positive_mem_P (i : Fin 24) : embedding (rootGeneratorInGroup 0 (positiveRoot i) 1) ∈ P := by
  fin_cases i
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 0) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 0) 1) = levi 0 :=
      Units.ext positiveVal0
    rw [he]
    exact mem_sup_right (levi_mem 0)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 1) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 1) 1) = levi 2 :=
      Units.ext positiveVal1
    rw [he]
    exact mem_sup_right (levi_mem 2)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 2) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 2) 1) = root 3 :=
      Units.ext positiveVal2
    rw [he]
    exact mem_sup_left (root_mem 3)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 3) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 3) 1) = root 13 :=
      Units.ext positiveVal3
    rw [he]
    exact mem_sup_left (root_mem 13)
  · exact mem_sup_right fourth_mem
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 5) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 5) 1) = root 12 :=
      Units.ext positiveVal5
    rw [he]
    exact mem_sup_left (root_mem 12)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 6) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 6) 1) = root 2 :=
      Units.ext positiveVal6
    rw [he]
    exact mem_sup_left (root_mem 2)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 7) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 7) 1) = root 14 :=
      Units.ext positiveVal7
    rw [he]
    exact mem_sup_left (root_mem 14)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 8) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 8) 1) = root 11 :=
      Units.ext positiveVal8
    rw [he]
    exact mem_sup_left (root_mem 11)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 9) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 9) 1) = root 4 :=
      Units.ext positiveVal9
    rw [he]
    exact mem_sup_left (root_mem 4)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 10) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 10) 1) = root 1 :=
      Units.ext positiveVal10
    rw [he]
    exact mem_sup_left (root_mem 1)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 11) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 11) 1) = root 15 :=
      Units.ext positiveVal11
    rw [he]
    exact mem_sup_left (root_mem 15)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 12) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 12) 1) = root 10 :=
      Units.ext positiveVal12
    rw [he]
    exact mem_sup_left (root_mem 10)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 13) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 13) 1) = root 6 :=
      Units.ext positiveVal13
    rw [he]
    exact mem_sup_left (root_mem 6)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 14) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 14) 1) = root 17 :=
      Units.ext positiveVal14
    rw [he]
    exact mem_sup_left (root_mem 17)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 15) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 15) 1) = root 16 :=
      Units.ext positiveVal15
    rw [he]
    exact mem_sup_left (root_mem 16)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 16) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 16) 1) = root 8 :=
      Units.ext positiveVal16
    rw [he]
    exact mem_sup_left (root_mem 8)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 17) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 17) 1) = root 18 :=
      Units.ext positiveVal17
    rw [he]
    exact mem_sup_left (root_mem 18)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 18) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 18) 1) = root 9 :=
      Units.ext positiveVal18
    rw [he]
    exact mem_sup_left (root_mem 9)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 19) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 19) 1) = root 19 :=
      Units.ext positiveVal19
    rw [he]
    exact mem_sup_left (root_mem 19)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 20) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 20) 1) = root 7 :=
      Units.ext positiveVal20
    rw [he]
    exact mem_sup_left (root_mem 7)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 21) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 21) 1) = root 20 :=
      Units.ext positiveVal21
    rw [he]
    exact mem_sup_left (root_mem 20)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 22) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 22) 1) = root 5 :=
      Units.ext positiveVal22
    rw [he]
    exact mem_sup_left (root_mem 5)
  · change embedding (rootGeneratorInGroup 0 (positiveRoot 23) 1) ∈ P
    have he : embedding (rootGeneratorInGroup 0 (positiveRoot 23) 1) = root 0 :=
      Units.ext positiveVal23
    rw [he]
    exact mem_sup_left (root_mem 0)

/-- All positive root curves lie in the original matrix parabolic. -/
theorem U_le_P : U ≤ P := by
  rw [U, map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro _ ⟨r,t,hr,rfl⟩
  obtain rfl | rfl := parameter_cases t
  · change embedding (rootGeneratorInGroup 0 r 0) ∈ P
    rw [parameter_zero,map_one]
    exact P.one_mem
  · obtain ⟨i,rfl⟩ := positive_exhaustive r hr
    exact positive_mem_P i

/-- Every generator of the original radical is a positive root in this same carrier. -/
theorem E_le_U : E ≤ U := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 23) 1,
      subset_closure ⟨positiveRoot 23,1,positivePos23,rfl⟩,Units.ext positiveVal23⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 10) 1,
      subset_closure ⟨positiveRoot 10,1,positivePos10,rfl⟩,Units.ext positiveVal10⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 6) 1,
      subset_closure ⟨positiveRoot 6,1,positivePos6,rfl⟩,Units.ext positiveVal6⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 2) 1,
      subset_closure ⟨positiveRoot 2,1,positivePos2,rfl⟩,Units.ext positiveVal2⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 9) 1,
      subset_closure ⟨positiveRoot 9,1,positivePos9,rfl⟩,Units.ext positiveVal9⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 22) 1,
      subset_closure ⟨positiveRoot 22,1,positivePos22,rfl⟩,Units.ext positiveVal22⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 13) 1,
      subset_closure ⟨positiveRoot 13,1,positivePos13,rfl⟩,Units.ext positiveVal13⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 20) 1,
      subset_closure ⟨positiveRoot 20,1,positivePos20,rfl⟩,Units.ext positiveVal20⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 16) 1,
      subset_closure ⟨positiveRoot 16,1,positivePos16,rfl⟩,Units.ext positiveVal16⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 18) 1,
      subset_closure ⟨positiveRoot 18,1,positivePos18,rfl⟩,Units.ext positiveVal18⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 12) 1,
      subset_closure ⟨positiveRoot 12,1,positivePos12,rfl⟩,Units.ext positiveVal12⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 8) 1,
      subset_closure ⟨positiveRoot 8,1,positivePos8,rfl⟩,Units.ext positiveVal8⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 5) 1,
      subset_closure ⟨positiveRoot 5,1,positivePos5,rfl⟩,Units.ext positiveVal5⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 3) 1,
      subset_closure ⟨positiveRoot 3,1,positivePos3,rfl⟩,Units.ext positiveVal3⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 7) 1,
      subset_closure ⟨positiveRoot 7,1,positivePos7,rfl⟩,Units.ext positiveVal7⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 11) 1,
      subset_closure ⟨positiveRoot 11,1,positivePos11,rfl⟩,Units.ext positiveVal11⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 15) 1,
      subset_closure ⟨positiveRoot 15,1,positivePos15,rfl⟩,Units.ext positiveVal15⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 14) 1,
      subset_closure ⟨positiveRoot 14,1,positivePos14,rfl⟩,Units.ext positiveVal14⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 17) 1,
      subset_closure ⟨positiveRoot 17,1,positivePos17,rfl⟩,Units.ext positiveVal17⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 19) 1,
      subset_closure ⟨positiveRoot 19,1,positivePos19,rfl⟩,Units.ext positiveVal19⟩
  · exact ⟨rootGeneratorInGroup 0 (positiveRoot 21) 1,
      subset_closure ⟨positiveRoot 21,1,positivePos21,rfl⟩,Units.ext positiveVal21⟩

theorem positive_levi_mem_U (i : Fin 2) : levi ⟨2*i.val,by omega⟩ ∈ U :=
  ⟨rootGeneratorInGroup 0 (typeF4SimpleRootIndex i.castSucc.castSucc) 1,
    subset_closure ⟨_,1,typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i.castSucc.castSucc).property,rfl⟩,positive_long i⟩

/-- Exact comparison of the canonical long-A2 parabolic and the original matrix group. -/
theorem parabolic_image : (longParabolic 0).map embedding = P := by
  apply le_antisymm
  · rw [longParabolic, Subgroup.map_sup]
    apply sup_le U_le_P
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨i,t,hi,rfl⟩
    change embedding (rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) t) ∈ P
    obtain rfl | rfl := parameter_cases t
    · rw [parameter_zero,map_one]
      exact P.one_mem
    · have hh := negative_long_mem (⟨i.val,hi⟩ : Fin 2)
      exact mem_sup_right hh
  · apply sup_le
    · exact E_le_U.trans (map_mono le_sup_left)
    · apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      have hp (j : Fin 2) : levi ⟨2*j.val,by omega⟩ ∈ (longParabolic 0).map embedding :=
        (map_mono le_sup_left) (positive_levi_mem_U j)
      have hn (j : Fin 2) : levi ⟨2*j.val+1,by omega⟩ ∈ (longParabolic 0).map embedding :=
        ⟨rootGeneratorInGroup 0 (-typeF4SimpleRootIndex j.castSucc.castSucc) 1,
          mem_sup_right (subset_closure ⟨j.castSucc.castSucc,1,j.isLt,rfl⟩),negative_long j⟩
      fin_cases i
      · exact hp 0
      · exact hn 0
      · exact hp 1
      · exact hn 1

/-- The comparison preserves the actual ambient matrix embedding. -/
def parabolicEquiv : longParabolic 0 ≃* P :=
  ((longParabolic 0).equivMapOfInjective embedding embedding_injective).trans
    (MulEquiv.subgroupCongr parabolic_image)

theorem parabolicEquiv_coe (x : longParabolic 0) :
    (parabolicEquiv x : Matˣ) = embedding x := by rfl

/-- The canonical positive subgroup becomes the literal subgroup U of P. -/
theorem parabolicEquiv_positive :
    (positiveInParabolic 0).map parabolicEquiv.toMonoidHom = U.subgroupOf P := by
  apply map_injective P.subtype_injective
  rw [map_subgroupOf_eq_of_le U_le_P, map_map]
  have he : P.subtype.comp parabolicEquiv.toMonoidHom =
      embedding.comp (longParabolic 0).subtype := by ext x; rfl
  rw [he, ← map_map, positiveInParabolic, map_subgroupOf_eq_of_le (show splitUnipotent 0 ≤ longParabolic 0 from le_sup_left)]
  rfl

end Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates.Canonical
