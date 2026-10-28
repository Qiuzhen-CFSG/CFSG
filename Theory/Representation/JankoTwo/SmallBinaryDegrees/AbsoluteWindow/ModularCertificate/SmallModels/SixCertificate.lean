module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Certificates
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.RankOne
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.SixCertificate.Checks

/-!
# The complete degree-six Hall--Janko matrix certificate

The checked ATLAS products give the five presentation relations and a positive
word of trace t. A polynomial in an explicit linear combination of words is
proved to be v lambda. Its left and right orbit bases, with P Pi = I and
Qi Q = I, yield the entire matrix algebra. Arithmetic evaluation transports all
identities to every characteristic-two field with t²=t+1, in every universe.

The final consumer applies the certificate to the literal Hall--Janko carrier;
presentation injectivity is required only for that independent descent step.
Source: ATLAS J2G1-f4r6aB0 and J2G1-P2; see SmallModels/source/README.md and
SixCertificate/source/README.md for attribution and witness conventions.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Arithmetic

namespace SixCertificate
variable {F : Type*} [Field F] [CharP F 2]

private theorem eval_codeWord (t : F) (ht : t ^ 2 = t + 1) (w : List Bool) :
    evalMatrix t (codeWord w) =
      wordValue (evalMatrix t SixData.A) (evalMatrix t SixData.B) w := by
  induction w with
  | nil => rw [codeWord, eval_one]; rfl
  | cons s w ih =>
    rw [codeWord, eval_product t ht, ih]
    cases s <;> rfl

private theorem eval_codePow (t : F) (ht : t ^ 2 = t + 1) (M : CodeMatrix 6) (n : ℕ) :
    evalMatrix t (codePow M n) = (evalMatrix t M) ^ n := by
  induction n with
  | zero => rw [codePow, eval_one, pow_zero]
  | succ n ih => rw [codePow, eval_product t ht, ih, pow_succ]

private theorem power_word_eq_one (t : F) (ht : t ^ 2 = t + 1)
    (w : List Bool) (k : ℕ) (h : codePow (codeWord w) k = codeOne) :
    wordValue (evalMatrix t SixData.A) (evalMatrix t SixData.B) w ^ k = 1 := by
  rw [← eval_codeWord t ht, ← eval_codePow t ht, h, eval_one]

/-- All five literal ATLAS relators, with the products in the order used by
`Presentation.Relations` and `MatrixRelations`. -/
theorem matrixRelations (t : F) (ht : t ^ 2 = t + 1) :
    MatrixRelations (evalMatrix t SixData.A) (evalMatrix t SixData.B) := by
  have h1 := power_word_eq_one t ht _ _ relation_1
  have h2 := power_word_eq_one t ht _ _ relation_2
  have h3 := power_word_eq_one t ht _ _ relation_3
  have h4 := power_word_eq_one t ht _ _ relation_4
  have h5 := power_word_eq_one t ht _ _ relation_5
  simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, mul_one] at h1 h2 h3 h4 h5
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · exact h3
  · simpa only [pow_two, mul_assoc] using h4
  · simpa only [pow_two, mul_assoc] using h5

private theorem codeLin_mem (t : F) (ht : t ^ 2 = t + 1)
    (S : Subalgebra F (Matrix (Fin 6) (Fin 6) F))
    (ha : evalMatrix t SixData.A ∈ S) (hb : evalMatrix t SixData.B ∈ S)
    (ws : List (List Bool)) (cs : List (Fin 4)) :
    evalMatrix t (codeLin ws cs) ∈ S := by
  induction ws generalizing cs with
  | nil => simp [codeLin, eval_zero]
  | cons w ws ih =>
    cases cs with
    | nil => simp [codeLin, eval_zero]
    | cons c cs =>
      rw [codeLin, eval_add, eval_scale t ht]
      refine S.add_mem (S.smul_mem ?_ _) (ih cs)
      rw [eval_codeWord t ht]
      exact wordValue_mem S _ _ ha hb w

private theorem codePoly_mem (t : F) (ht : t ^ 2 = t + 1)
    (S : Subalgebra F (Matrix (Fin 6) (Fin 6) F)) (T : CodeMatrix 6)
    (hT : evalMatrix t T ∈ S) (cs : List (Fin 4)) :
    evalMatrix t (codePoly cs T) ∈ S := by
  induction cs with
  | nil => simp [codePoly, eval_zero]
  | cons c cs ih =>
    rw [codePoly, eval_add, eval_scale t ht, eval_product t ht, eval_one]
    exact S.add_mem (S.smul_mem S.one_mem _) (S.mul_mem hT ih)

/-- The checked polynomial in the specified linear combination of words
places the literal outer product in every algebra containing A and B. -/
theorem rankOne_mem (t : F) (ht : t ^ 2 = t + 1)
    (S : Subalgebra F (Matrix (Fin 6) (Fin 6) F))
    (ha : evalMatrix t SixData.A ∈ S) (hb : evalMatrix t SixData.B ∈ S) :
    Matrix.vecMulVec (evalVector t SixData.v) (evalVector t SixData.lam) ∈ S := by
  have hT := codeLin_mem t ht S ha hb SixData.algebraWords SixData.algebraCoefficients
  have hq := codePoly_mem t ht S _ hT SixData.polynomial
  rwa [rankOne_identity, eval_outer t ht] at hq

/-- The left words in Data already have the reversal required for column action. -/
theorem left_orbit_eval (t : F) (ht : t ^ 2 = t + 1) (i : Fin 6) :
    (wordValue (evalMatrix t SixData.A) (evalMatrix t SixData.B) (SixData.leftWords i)).mulVec
      (evalVector t SixData.v) = fun k => evalMatrix t SixData.P k i := by
  rw [← eval_codeWord t ht, ← eval_mulVec t ht, left_orbit]
  rfl

theorem right_orbit_eval (t : F) (ht : t ^ 2 = t + 1) (i : Fin 6) :
    Matrix.vecMul (evalVector t SixData.lam)
      (wordValue (evalMatrix t SixData.A) (evalMatrix t SixData.B) (SixData.rightWords i)) =
      evalMatrix t SixData.Q i := by
  rw [← eval_codeWord t ht, ← eval_vecMul t ht, right_orbit]
  rfl

/-- The two orbit bases and their indicated one-sided inverses span all matrices. -/
theorem density (t : F) (ht : t ^ 2 = t + 1) :
    Algebra.adjoin F ({evalMatrix t SixData.A, evalMatrix t SixData.B} :
      Set (Matrix (Fin 6) (Fin 6) F)) = ⊤ := by
  apply density_of_rankOne (evalMatrix t SixData.A) (evalMatrix t SixData.B)
    (evalVector t SixData.v) (evalVector t SixData.lam)
    (evalMatrix t SixData.P) (evalMatrix t SixData.Pi)
    (evalMatrix t SixData.Q) (evalMatrix t SixData.Qi)
    SixData.leftWords SixData.rightWords
  · exact rankOne_mem t ht _ (Algebra.subset_adjoin (by simp))
      (Algebra.subset_adjoin (by simp))
  · exact left_orbit_eval t ht
  · exact right_orbit_eval t ht
  · rw [← eval_product t ht, inverse_P, eval_one]
  · rw [← eval_product t ht, inverse_Q, eval_one]

/-- The positive word in Data has the nonbinary trace t. -/
theorem trace_eq (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t SixData.A) (evalMatrix t SixData.B) SixData.traceWord).trace =
      coefficient t SixData.traceCode := by
  rw [← eval_codeWord t ht, ← eval_trace, trace_identity]

end SixCertificate

universe v

/-- The complete numerical certificate, uniform in the field and its universe. -/
theorem six_parameterCertificate :
    ParameterCertificate.{v} SixData.A SixData.B SixData.traceWord SixData.traceCode := by
  intro F _ _ t ht
  exact ⟨SixCertificate.matrixRelations t ht, SixCertificate.density t ht,
    SixCertificate.trace_eq t ht⟩

/-- Applying the numerical certificate to the literal carrier gives the two
inequivalent degree-six actions once the independent presentation descent is available. -/
theorem exists_six_pair
    (hp : Function.Injective
      Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.Presentation.toCarrier)
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2] :
    ∃ ρ σ : Representation F Sporadic.LeechRelated.J2.Carrier (Fin 6 → F),
      IsIrreducible ρ ∧ IsIrreducible σ ∧ IsEmpty (ρ.Equiv σ) :=
  exists_pair_of_certificate hp SixData.A SixData.B SixData.traceWord SixData.traceCode
    SixData.traceCode_nonbinary six_parameterCertificate F

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
