module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.Checker
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.CommutatorProducts
import Mathlib.Tactic.FinCases

/-!
# Product assembly for the first seven ATLAS HS matrix words

The first seven source relators are powers of short words. Reusing intermediate
products reduces their numerical certification to 29 matrix products. The
assembly below expands the unchanged literal source words, so it also checks the
source order and the convention a⁻¹b⁻¹ab for commutators. In the raw matrix
alphabet a⁻¹ is A and b⁻¹ is the shared candidate I; neither inverse identity is
assumed here.

The three complete numerical certificates discharge all 29 products, giving
the unconditional `smallWords` theorem. The conditional `smallWords_of_products`
interface is retained. Source: the retained ATLAS HSG1-P1.M; see
`SmallWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
open SmallWordProducts

private theorem fifth_power {M : Type*} [Monoid M] (x x2 x4 : M)
    (h2 : x * x = x2) (h4 : x2 * x2 = x4) (h5 : x4 * x = 1) : x ^ 5 = 1 := by
  calc
    x ^ 5 = ((x * x) * (x * x)) * x := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h2, h4, h5]

private theorem tenth_power {M : Type*} [Monoid M] (x x2 x4 x5 : M)
    (h2 : x * x = x2) (h4 : x2 * x2 = x4) (h5 : x4 * x = x5)
    (h10 : x5 * x5 = 1) : x ^ 10 = 1 := by
  calc
    x ^ 10 = (((x * x) * (x * x)) * x) * (((x * x) * (x * x)) * x) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h2, h4, h5, h10]

private theorem eleventh_power {M : Type*} [Monoid M] (x x2 x4 x8 x10 : M)
    (h2 : x * x = x2) (h4 : x2 * x2 = x4) (h8 : x4 * x4 = x8)
    (h10 : x8 * x2 = x10) (h11 : x10 * x = 1) : x ^ 11 = 1 := by
  calc
    x ^ 11 = ((((x * x) * (x * x)) * ((x * x) * (x * x))) * (x * x)) * x := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h2, h4, h8, h10, h11]

private theorem third_power {M : Type*} [Monoid M] (x x2 : M)
    (h2 : x * x = x2) (h3 : x2 * x = 1) : x ^ 3 = 1 := by
  simpa only [pow_succ, pow_zero, one_mul, h2] using h3

private theorem sixth_power {M : Type*} [Monoid M] (x x2 x3 : M)
    (h2 : x * x = x2) (h3 : x2 * x = x3) (h6 : x3 * x3 = 1) : x ^ 6 = 1 := by
  calc
    x ^ 6 = ((x * x) * x) * ((x * x) * x) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h2, h3, h6]

/-- The three independent product certificates discharge exactly source
indices 0–6 of `matrixWord`. No inverse or other relator is assumed. -/
theorem smallWords_of_products (g : GeneratorProducts) (p : AlternatingProducts)
    (c : CommutatorProducts) : ∀ i : Fin 7, matrixWord ⟨i.val, by omega⟩ = 1 := by
  have ha : matrixA ^ 2 = 1 := by simpa only [pow_two] using g.a_a
  have hb : matrixB ^ 5 = 1 :=
    fifth_power matrixB b2 inverseMatrix g.b_b g.b2_b2 g.inverse_b
  have hab : (matrixA * matrixB) ^ 11 = 1 := by
    rw [p.a_b]
    exact eleventh_power ab ab2 ab4 ab8 ab10 p.ab_ab p.ab2_ab2 p.ab4_ab4
      p.ab8_ab2 p.ab10_ab
  have habb : (matrixA * matrixB * matrixB) ^ 10 = 1 := by
    rw [p.a_b, p.ab_b]
    exact tenth_power abb abb2 abb4 abb5 p.abb_abb p.abb2_abb2 p.abb4_abb p.abb5_abb5
  have hcomm : (matrixA * inverseMatrix * matrixA * matrixB) ^ 5 = 1 := by
    rw [mul_assoc (matrixA * inverseMatrix), c.a_inverse, p.a_b, c.ai_ab]
    exact fifth_power comm comm2 comm4 c.comm_comm c.comm2_comm2 c.comm4_comm
  have hmixed : ((matrixA * inverseMatrix) * (matrixA * inverseMatrix) *
      ((matrixA * matrixB) * (matrixA * matrixB))) ^ 3 = 1 := by
    rw [c.a_inverse, p.a_b, c.ai_ai, p.ab_ab, c.ai2_ab2]
    exact third_power mixed mixed2 c.mixed_mixed c.mixed2_mixed
  have hsquareComm : ((matrixA * inverseMatrix * inverseMatrix) *
      (matrixA * matrixB * matrixB)) ^ 6 = 1 := by
    rw [c.a_inverse, c.ai_inverse, p.a_b, p.ab_b, c.aii_abb]
    exact sixth_power squareComm squareComm2 squareComm3 c.squareComm_squareComm
      c.squareComm2_squareComm c.squareComm3_squareComm3
  intro i
  fin_cases i
  · change matrixA * (matrixA * (1)) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using ha
  · change matrixB * (matrixB * (matrixB * (matrixB * (matrixB * (1))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using hb
  · change matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (matrixB * (1)))))))))))))))))))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using hab
  · change matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (matrixA * (matrixB * (matrixB * (1)))))))))))))))))))))))))))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using habb
  · change matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (matrixB * (1)))))))))))))))))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using hcomm
  · change matrixA * (inverseMatrix * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (matrixB * (matrixA * (inverseMatrix * (matrixA * (inverseMatrix * (matrixA * (matrixB * (matrixA * (matrixB * (1)))))))))))))))))))))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using hmixed
  · change matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (matrixA * (inverseMatrix * (inverseMatrix * (matrixA * (matrixB * (matrixB * (1)))))))))))))))))))))))))))))))))))) = 1
    simpa only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc] using hsquareComm

/-- The first seven literal ATLAS matrix words equal the identity, with every
finite product obligation discharged and no inverse or relator assumed. -/
theorem smallWords : ∀ i : Fin 7, matrixWord ⟨i.val, by omega⟩ = 1 :=
  smallWords_of_products generatorProducts alternatingProducts commutatorProducts

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate
