module
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.GeneratorTables
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.RootNormalizer
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.Sp6Presentation

/-!
# A binary symplectic section in every characteristic-two F4 model

Eight literal signed simple root elements are compared with integral Geck
matrices and then with the checked binary word certificates. The seven
relations give a homomorphism from Sp₆(2). Its first generator is a simple
root element which survives the actual central quotient, so binary
simplicity makes the homomorphism faithful.

The two generators centralize a specified conjugate of a simple root
involution. This involution is noncentral, so its cyclic subgroup has a
proper normalizer containing the symplectic image. The resulting
`NormalizerSection` is in the original exceptional central quotient and
works over every finite field of characteristic two, including F₂.

Sources: GLS3 §1.12 and §2.6; the proved ATLAS Sp₆(2) presentation in
`SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness`;
Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.LieType.SourceLevi.F4
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
open ExceptionalSplit Subgroup
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg

abbrev Cover (F : Type*) [Field F] := rootGenerated typeF4RootPairing typeF4RootPairing_base F
variable (F : Type*) [Field F] [CharP F 2]

def positive (i : Fin 4) : Cover F :=
  elementaryRoot typeF4RootPairing typeF4RootPairing_base F (typeF4RootPairing_baseEquiv i) 1

def negative (i : Fin 4) : Cover F :=
  elementaryRoot typeF4RootPairing typeF4RootPairing_base F
    (-(typeF4RootPairing_baseEquiv i) : typeF4Roots) 1

def generator : Fin 8 → Cover F :=
  ![positive F 0, negative F 0, positive F 1, negative F 1,
    positive F 2, negative F 2, positive F 3, negative F 3]

private def matrixEmbedding : Cover F →* (Matrix (Fin 52) (Fin 52) F)ˣ :=
  (Units.map (reindex (S := F)).toMonoidHom).comp (Cover F).subtype

omit [CharP F 2] in
private theorem matrixEmbedding_injective : Function.Injective (matrixEmbedding F) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply (reindex (S := F)).injective
  exact congrArg Units.val h

private def binaryMap : WordCertificates.Matˣ →* (Matrix (Fin 52) (Fin 52) F)ˣ :=
  Units.map (ZMod.castHom (dvd_refl 2) F).mapMatrix.toMonoidHom

omit [CharP F 2] in
private theorem positive_matrix (i : Fin 4) :
    reindex ((positive F i).val.val) =
      (Matrices.positiveInteger i).map (Int.castRingHom F) := by
  change reindex (rootCurveUnit (integralChevalleyRootOperators
      (P := typeF4RootPairing) (b := typeF4RootPairing_base))
      (typeF4RootPairing_baseEquiv i : typeF4Roots) (1 : F)).val = _
  rw [rootCurveUnit_simple, positiveUnit_val]
  exact Matrices.positive_one i

omit [CharP F 2] in
private theorem negative_matrix (i : Fin 4) :
    reindex ((negative F i).val.val) =
      (Matrices.negativeInteger i).map (Int.castRingHom F) := by
  change reindex (rootCurveUnit (integralChevalleyRootOperators
      (P := typeF4RootPairing) (b := typeF4RootPairing_base))
      (-(typeF4RootPairing_baseEquiv i) : typeF4Roots) (1 : F)).val = _
  rw [rootCurveUnit_neg_simple, negativeUnit_val]
  exact Matrices.negative_one i

private theorem generator_matrix (j : Fin 8) :
    matrixEmbedding F (generator F j) = binaryMap F (WordCertificates.generator j) := by
  apply Units.ext
  change reindex ((generator F j).val.val) =
    (WordCertificates.generator j).val.map (ZMod.castHom (dvd_refl 2) F)
  rw [WordCertificates.generator_val, ← GeneratorTables.integer_cast_decode]
  have hcast (A : Matrix (Fin 52) (Fin 52) ℤ) :
      (A.map (Int.castRingHom (ZMod 2))).map (ZMod.castHom (dvd_refl 2) F) =
        A.map (Int.castRingHom F) := by ext i k; simp
  rw [hcast]
  fin_cases j <;>
    simp only [generator, Matrices.integerGenerator, Matrix.cons_val, Fin.reduceFinMk]
  · exact positive_matrix F 0
  · exact negative_matrix F 0
  · exact positive_matrix F 1
  · exact negative_matrix F 1
  · exact positive_matrix F 2
  · exact negative_matrix F 2
  · exact positive_matrix F 3
  · exact negative_matrix F 3


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
def modelA : ExceptionalSplit.F4 F := projection _ _ F (a F)

/-- The second generator, with the same prescribed root word. -/
def modelB : ExceptionalSplit.F4 F := projection _ _ F (b F)

/-- The specified root involution conjugated by the actual Weyl word. -/
def modelZ : ExceptionalSplit.F4 F := projection _ _ F (z F)

omit [CharP F 2] in
theorem modelA_ne_one : modelA F ≠ 1 :=
  rootElement_simple_one_ne_one (typeF4RootPairing_baseEquiv 1)

omit [CharP F 2] in
theorem modelZ_not_mem_center : modelZ F ∉ center (ExceptionalSplit.F4 F) := by
  intro hc
  have h := (inferInstance : (center (ExceptionalSplit.F4 F)).Normal).conj_mem'
    (modelZ F) hc (projection _ _ F (w F))
  have he : (projection _ _ F (w F))⁻¹ * modelZ F * projection _ _ F (w F) =
      rootElement typeF4RootPairing typeF4RootPairing_base F
        (typeF4RootPairing_baseEquiv 0) 1 := by
    simp only [modelZ, z, map_mul, map_inv]
    group
    rfl
  rw [he] at h
  exact rootElement_simple_one_not_mem_center_model (typeF4RootPairing_baseEquiv 0) h

theorem modelZ_order : orderOf (modelZ F) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · have hx : (generator F 0) ^ 2 = 1 := by
      change elementaryRoot typeF4RootPairing typeF4RootPairing_base F
        (typeF4RootPairing_baseEquiv 0) 1 ^ 2 = 1
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
def normalizerSection [Finite F] : NormalizerSection (ExceptionalSplit.F4 F)
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

end Theory.SpecificGroups.LieType.SourceLevi.F4
end
