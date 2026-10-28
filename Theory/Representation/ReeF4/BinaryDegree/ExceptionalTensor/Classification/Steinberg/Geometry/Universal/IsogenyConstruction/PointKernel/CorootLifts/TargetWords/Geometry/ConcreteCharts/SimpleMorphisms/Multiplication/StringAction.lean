module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Multiplication.RootStrings
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Multiplication.DividedStrings

/-!
# Multiplication on the independent root-string columns

The literal polynomial matrix acts on each independent string by the divided
coefficients. The string coordinates identify every nonzero entry and show that
there are no terms outside that string. Convolving these columns proves the
multiplication law over any commutative coefficient ring.
Source: the integral root-string construction behind GLS3, Remark 1.12.10.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
local instance stringActionNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg
variable {k : Type*} [CommRing k]
variable {i : typeF4RootPairing_base.support} {j : Root}

/-- The root basis vector at a specified position of an independent string. -/
noncomputable def stringVector
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (t : Fin (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j + 1)) : BasisIndex → k :=
  Pi.single (Sum.inr (rootStringIdx i j hlin t (Nat.le_of_lt_succ t.isLt))) 1

lemma string_column
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (q : Fin (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j + 1))
    (A : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i A *ᵥ stringVector hlin q =
      ∑ r : Fin (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j + 1),
        dividedStringEntry (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) q r A •
          stringVector hlin r := by
  classical
  have hne := independent_iff.mp (linearIndependent_rootStringIdx hlin (Nat.le_of_lt_succ q.isLt))
  have hn : rootStringIdx i j hlin q (Nat.le_of_lt_succ q.isLt) ≠
      typeF4RootPairing.reflectionPerm i i := hne.2
  ext (x | x)
  · simp [stringVector, simpleSL2Matrix, hne.1, hn, eq_comm]
  · simp only [stringVector, Matrix.mulVec_single_one, Matrix.col_apply,
      simpleSL2Matrix, Matrix.of_apply, if_neg hne.1, if_neg hne.2,
      ← same_bottom_iff, rootStringIdx_same_bottom, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [rootStringIdx_length, chainBotCoeff_rootStringIdx]
    by_cases hx : typeF4RootPairing.chainBotIdx i x = typeF4RootPairing.chainBotIdx i j
    · rw [if_pos hx]
      let r : Fin (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j + 1) :=
        ⟨typeF4RootPairing.chainBotCoeff i x, Nat.lt_succ_of_le (same_bottom_bound hlin hx)⟩
      have heq : rootStringIdx i j hlin r (Nat.le_of_lt_succ r.isLt) = x :=
        rootStringIdx_eq_of_same_bottom hlin hx
      rw [Finset.sum_eq_single r]
      · simp [heq, r]
      · intro t _ htr
        have ht : rootStringIdx i j hlin t (Nat.le_of_lt_succ t.isLt) ≠ x := by
          intro h
          apply htr
          apply Fin.ext
          exact rootStringIdx_injective hlin _ _ (h.trans heq.symm)
        simp [Ne.symm ht]
      · simp
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro t _
      have ht : rootStringIdx i j hlin t (Nat.le_of_lt_succ t.isLt) ≠ x := by
        intro h
        apply hx
        rw [← h]
        exact rootStringIdx_same_bottom hlin _
      simp [Ne.symm ht]

lemma string_column_mul
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (q : Fin (typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j + 1))
    (A B : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i (A * B) *ᵥ stringVector hlin q =
      simpleSL2Matrix i A *ᵥ (simpleSL2Matrix i B *ᵥ stringVector hlin q) := by
  classical
  simp only [string_column, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_smul]
  congr 1
  rw [dividedStringEntry_mul_le_three _ _ _
    (typeF4RootPairing.chainBotCoeff_add_chainTopCoeff_le_three)
    (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ r.isLt),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

lemma independent_column_mul
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (A B : Matrix (Fin 2) (Fin 2) k) :
    simpleSL2Matrix i (A * B) *ᵥ (Pi.single (Sum.inr j) 1) =
      simpleSL2Matrix i A *ᵥ (simpleSL2Matrix i B *ᵥ (Pi.single (Sum.inr j) 1)) := by
  have h := string_column_mul hlin
    ⟨typeF4RootPairing.chainBotCoeff i j, Nat.lt_succ_of_le (Nat.le_add_right _ _)⟩ A B
  simpa only [stringVector, rootStringIdx_position] using h

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
