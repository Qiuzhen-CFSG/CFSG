module
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.GeneratorTables
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.WordCertificates
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.RawMatrices
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.RootNormalizer
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.Sp6Presentation

/-!
# The actual binary symplectic section of split E6 in characteristic two

The signed simple roots at nodes 3, 2, {1,4}, {0,5} give the eight folded
matrices. Their integral native Geck tables agree with the checked binary
word certificates. Scalar extension proves the seven Sp6(2) relations and
the two centralizing identities over every field of characteristic two.
The first generator is the actual simple root at node 2 and survives the
central quotient, so the binary symplectic homomorphism is faithful.

The specified conjugate of the root at node 3 is a noncentral involution.
Its proper normalizer contains the symplectic image. The rank-one braid
and distinctness statements at the two graph-fixed nodes additionally
supply the literal twisted E6 center-quotient construction.

Sources: GLS3 §§1.12, 2.4, 2.6; the proved ATLAS Sp6(2) presentation;
Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.LieType.SourceLevi.E6
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Operators Operators.Curves
open ExceptionalSplit Subgroup
attribute [local instance] Classical.decEq
local instance : Fintype typeE6Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeE6Roots := typeE6RootPairing.indexNeg

abbrev Cover (F : Type*) [Field F] := rootGenerated typeE6RootPairing typeE6RootPairing_base F
private theorem packed_zero_braid :
    WordCertificates.generator 0 * WordCertificates.generator 1 * WordCertificates.generator 0 =
      WordCertificates.generator 1 * WordCertificates.generator 0 * WordCertificates.generator 1 := by
  apply Units.ext
  simpa only [Units.val_mul, WordCertificates.generator_val,
    ← RawMatrices.folded_0, ← RawMatrices.folded_1] using RawMatrices.braid_3

private theorem packed_two_braid :
    WordCertificates.generator 2 * WordCertificates.generator 3 * WordCertificates.generator 2 =
      WordCertificates.generator 3 * WordCertificates.generator 2 * WordCertificates.generator 3 := by
  apply Units.ext
  simpa only [Units.val_mul, WordCertificates.generator_val,
    ← RawMatrices.folded_2, ← RawMatrices.folded_3] using RawMatrices.braid_2

private theorem packed_zero_distinct : WordCertificates.generator 0 ≠ WordCertificates.generator 1 := by
  intro h
  apply RawMatrices.distinct_3
  rw [RawMatrices.folded_0, RawMatrices.folded_1]
  simpa only [WordCertificates.generator_val] using congrArg Units.val h

private theorem packed_two_distinct : WordCertificates.generator 2 ≠ WordCertificates.generator 3 := by
  intro h
  apply RawMatrices.distinct_2
  rw [RawMatrices.folded_2, RawMatrices.folded_3]
  simpa only [WordCertificates.generator_val] using congrArg Units.val h

variable (F : Type*) [Field F] [CharP F 2]

def positive (i : Fin 6) : Cover F :=
  elementaryRoot typeE6RootPairing typeE6RootPairing_base F (typeE6RootPairing_baseEquiv i) 1

def negative (i : Fin 6) : Cover F :=
  elementaryRoot typeE6RootPairing typeE6RootPairing_base F
    (-(typeE6RootPairing_baseEquiv i) : typeE6Roots) 1

def rawGenerator : Fin 12 → Cover F :=
  ![positive F 0, negative F 0, positive F 1, negative F 1,
    positive F 2, negative F 2, positive F 3, negative F 3,
    positive F 4, negative F 4, positive F 5, negative F 5]

def generator : Fin 8 → Cover F :=
  ![rawGenerator F 6, rawGenerator F 7, rawGenerator F 4, rawGenerator F 5,
    rawGenerator F 2 * rawGenerator F 8, rawGenerator F 3 * rawGenerator F 9,
    rawGenerator F 0 * rawGenerator F 10, rawGenerator F 1 * rawGenerator F 11]

private def matrixEmbedding : Cover F →* (Matrix (Fin 78) (Fin 78) F)ˣ :=
  (Units.map (reindex (S := F)).toMonoidHom).comp (Cover F).subtype

omit [CharP F 2] in
private theorem matrixEmbedding_injective : Function.Injective (matrixEmbedding F) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply (reindex (S := F)).injective
  exact congrArg Units.val h

private def binaryMap : WordCertificates.Matˣ →* (Matrix (Fin 78) (Fin 78) F)ˣ :=
  Units.map (ZMod.castHom (dvd_refl 2) F).mapMatrix.toMonoidHom

private theorem binaryMap_injective : Function.Injective (binaryMap F) := by
  intro x y h
  apply Units.ext
  ext r c
  apply (ZMod.castHom (dvd_refl 2) F).injective
  exact congrArg (fun M : (Matrix (Fin 78) (Fin 78) F)ˣ => M.val r c) h

omit [CharP F 2] in
private theorem positive_matrix (i : Fin 6) :
    reindex ((positive F i).val.val) =
      (Curves.positiveInteger i).map (Int.castRingHom F) := by
  change reindex (rootCurveUnit (integralChevalleyRootOperators
      (P := typeE6RootPairing) (b := typeE6RootPairing_base))
      (typeE6RootPairing_baseEquiv i : typeE6Roots) (1 : F)).val = _
  rw [rootCurveUnit_simple, positiveUnit_val]
  exact Curves.positive_one i

omit [CharP F 2] in
private theorem negative_matrix (i : Fin 6) :
    reindex ((negative F i).val.val) =
      (Curves.negativeInteger i).map (Int.castRingHom F) := by
  change reindex (rootCurveUnit (integralChevalleyRootOperators
      (P := typeE6RootPairing) (b := typeE6RootPairing_base))
      (-(typeE6RootPairing_baseEquiv i) : typeE6Roots) (1 : F)).val = _
  rw [rootCurveUnit_neg_simple, negativeUnit_val]
  exact Curves.negative_one i

private theorem raw_generator_matrix (j : Fin 12) :
    reindex ((rawGenerator F j).val.val) =
      (Thompson.BinaryMatrix.decode 78 (RawMatrices.rows j)).map
        (ZMod.castHom (dvd_refl 2) F) := by
  rw [← GeneratorTables.integer_cast_decode]
  have hcast (A : Matrix (Fin 78) (Fin 78) ℤ) :
      (A.map (Int.castRingHom (ZMod 2))).map (ZMod.castHom (dvd_refl 2) F) =
        A.map (Int.castRingHom F) := by ext i k; simp
  rw [hcast]
  fin_cases j <;>
    simp only [rawGenerator, Curves.integerGenerator, Matrix.cons_val, Fin.reduceFinMk]
  · exact positive_matrix F 0
  · exact negative_matrix F 0
  · exact positive_matrix F 1
  · exact negative_matrix F 1
  · exact positive_matrix F 2
  · exact negative_matrix F 2
  · exact positive_matrix F 3
  · exact negative_matrix F 3
  · exact positive_matrix F 4
  · exact negative_matrix F 4
  · exact positive_matrix F 5
  · exact negative_matrix F 5

private theorem generator_matrix (j : Fin 8) :
    matrixEmbedding F (generator F j) = binaryMap F (WordCertificates.generator j) := by
  apply Units.ext
  change reindex ((generator F j).val.val) =
    (WordCertificates.generator j).val.map (ZMod.castHom (dvd_refl 2) F)
  rw [WordCertificates.generator_val]
  fin_cases j <;>
    simp only [generator, Matrix.cons_val, Fin.reduceFinMk, Subgroup.coe_mul,
      Units.val_mul, map_mul, raw_generator_matrix]
  · exact congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F)) RawMatrices.folded_0
  · exact congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F)) RawMatrices.folded_1
  · exact congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F)) RawMatrices.folded_2
  · exact congrArg (fun M => M.map (ZMod.castHom (dvd_refl 2) F)) RawMatrices.folded_3
  · simpa only [← RingHom.mapMatrix_apply, map_mul] using
      congrArg (ZMod.castHom (dvd_refl 2) F).mapMatrix RawMatrices.folded_4
  · simpa only [← RingHom.mapMatrix_apply, map_mul] using
      congrArg (ZMod.castHom (dvd_refl 2) F).mapMatrix RawMatrices.folded_5
  · simpa only [← RingHom.mapMatrix_apply, map_mul] using
      congrArg (ZMod.castHom (dvd_refl 2) F).mapMatrix RawMatrices.folded_6
  · simpa only [← RingHom.mapMatrix_apply, map_mul] using
      congrArg (ZMod.castHom (dvd_refl 2) F).mapMatrix RawMatrices.folded_7

/-- The two signed roots at the fixed node 3 satisfy the actual rank-one braid. -/
theorem generator_zero_braid :
    generator F 0 * generator F 1 * generator F 0 =
      generator F 1 * generator F 0 * generator F 1 := by
  apply matrixEmbedding_injective F
  simp only [map_mul, generator_matrix]
  simpa only [map_mul] using congrArg (binaryMap F) packed_zero_braid

/-- The two signed roots at the fixed node 2 satisfy the actual rank-one braid. -/
theorem generator_two_braid :
    generator F 2 * generator F 3 * generator F 2 =
      generator F 3 * generator F 2 * generator F 3 := by
  apply matrixEmbedding_injective F
  simp only [map_mul, generator_matrix]
  simpa only [map_mul] using congrArg (binaryMap F) packed_two_braid

/-- The signed roots at node 3 are distinct in the literal split root group. -/
theorem generator_zero_distinct : generator F 0 ≠ generator F 1 := by
  intro h
  apply packed_zero_distinct
  apply binaryMap_injective F
  simpa only [generator_matrix] using congrArg (matrixEmbedding F) h

/-- The signed roots at node 2 are distinct in the literal split root group. -/
theorem generator_two_distinct : generator F 2 ≠ generator F 3 := by
  intro h
  apply packed_two_distinct
  apply binaryMap_injective F
  simpa only [generator_matrix] using congrArg (matrixEmbedding F) h


def a : Cover F := generator F 2
def b : Cover F := (WordCertificates.bWord.map (generator F)).prod
def w : Cover F := (WordCertificates.wWord.map (generator F)).prod
def z : Cover F := w F * generator F 0 * (w F)⁻¹

private theorem matrix_a : matrixEmbedding F (a F) = binaryMap F WordCertificates.a :=
  generator_matrix F 2
private theorem matrix_b : matrixEmbedding F (b F) = binaryMap F WordCertificates.b := by
  simp only [b, WordCertificates.b, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun j _ => generator_matrix F j)
private theorem matrix_w : matrixEmbedding F (w F) = binaryMap F WordCertificates.w := by
  simp only [w, WordCertificates.w, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun j _ => generator_matrix F j)
private theorem matrix_z : matrixEmbedding F (z F) = binaryMap F WordCertificates.z := by
  simp only [z, WordCertificates.z, map_mul, map_inv, matrix_w, generator_matrix]

open SymplecticSix.UniversalDoubleCover

theorem relators (i : Fin 7) : KernelPresentation.word (a F) (b F) i = 1 := by
  apply matrixEmbedding_injective F
  rw [KernelPresentation.map_word, matrix_a, matrix_b,
    ← KernelPresentation.map_word, WordCertificates.relators, map_one, map_one]

theorem commute_a_z : Commute (a F) (z F) := by
  apply matrixEmbedding_injective F
  simp only [map_mul, matrix_a, matrix_z]
  exact WordCertificates.commute_a_z.map (binaryMap F)

theorem commute_b_z : Commute (b F) (z F) := by
  apply matrixEmbedding_injective F
  simp only [map_mul, matrix_b, matrix_z]
  exact WordCertificates.commute_b_z.map (binaryMap F)

/-- The first generator in the literal exceptional central quotient. -/
def modelA : ExceptionalSplit.E6 F := projection _ _ F (a F)

/-- The second generator, with the same prescribed root word. -/
def modelB : ExceptionalSplit.E6 F := projection _ _ F (b F)

/-- The specified root involution conjugated by the actual Weyl word. -/
def modelZ : ExceptionalSplit.E6 F := projection _ _ F (z F)

omit [CharP F 2] in
theorem modelA_ne_one : modelA F ≠ 1 :=
  rootElement_simple_one_ne_one (typeE6RootPairing_baseEquiv 2)

omit [CharP F 2] in
theorem modelZ_not_mem_center : modelZ F ∉ center (ExceptionalSplit.E6 F) := by
  intro hc
  have h := (inferInstance : (center (ExceptionalSplit.E6 F)).Normal).conj_mem'
    (modelZ F) hc (projection _ _ F (w F))
  have he : (projection _ _ F (w F))⁻¹ * modelZ F * projection _ _ F (w F) =
      rootElement typeE6RootPairing typeE6RootPairing_base F
        (typeE6RootPairing_baseEquiv 3) 1 := by
    simp only [modelZ, z, map_mul, map_inv]
    group
    rfl
  rw [he] at h
  exact rootElement_simple_one_not_mem_center_model (typeE6RootPairing_baseEquiv 3) h

theorem modelZ_order : orderOf (modelZ F) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · have hx : (generator F 0) ^ 2 = 1 := by
      change elementaryRoot typeE6RootPairing typeE6RootPairing_base F
        (typeE6RootPairing_baseEquiv 3) 1 ^ 2 = 1
      have hone : (1 : F) + 1 = 0 := by
        calc
          (1 : F) + 1 = (2 : ℕ) := by norm_num
          _ = 0 := CharP.cast_eq_zero F 2
      rw [pow_two, ← elementaryRoot_add, hone, elementaryRoot_zero]
    have hz : z F ^ 2 = 1 := by
      rw [z, conj_pow, hx]
      group
    exact (map_pow (projection _ _ F) (z F) 2).symm.trans
      ((congrArg (projection _ _ F) hz).trans (map_one _))
  · intro h
    exact modelZ_not_mem_center F (h ▸ (center _).one_mem)

/-- The concrete binary symplectic section in the proper normalizer of the
specified conjugate root involution, over every finite characteristic-two field. -/
def normalizerSection [Finite F] : NormalizerSection (ExceptionalSplit.E6 F)
    (SymplecticSix.PSp (ZMod 2)) :=
  Sp6Presentation.normalizerSection (modelA F) (modelB F) (modelZ F)
    (fun i => by
      change KernelPresentation.word (projection _ _ F (a F))
        (projection _ _ F (b F)) i = 1
      rw [← KernelPresentation.map_word, relators, map_one])
    (modelA_ne_one F) (modelZ_order F) (modelZ_not_mem_center F)
    ((commute_a_z F).map (projection _ _ F))
    ((commute_b_z F).map (projection _ _ F))

theorem normalizerSection_twoSubgroup [Finite F] :
    (normalizerSection F).twoSubgroup = zpowers (modelZ F) :=
  Sp6Presentation.normalizerSection_twoSubgroup _ _ _ _ _ _ _ _ _

end Theory.SpecificGroups.LieType.SourceLevi.E6
end
