module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic.Certificates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic.Enumeration
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Exact multiplication coordinates of the intrinsic quartic

The 210 coefficients and their ordering are the unchanged data published by
`SeedCentralizer/explore.py`; see `Quartic/source/README.md`. The finite column
certificates and the cyclic commutant theorem prove each full matrix identity.
Commutativity makes the product invariant under permutation of its four slots,
and a repeated slot gives zero by the square-zero identity. Sorting then gives
the top-operator coordinate for every tuple, with its normalization fixed by
entry (0,0). These are the coordinate identities for the alternating four-form;
no preservation by an ambient centralizer is asserted here.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate

/-- The product in the four specified positions; arbitrary repetitions are allowed. -/
def quarticProduct (t : Fin 4 → Fin 10) : SmallMatrix :=
  operator (t 0) * operator (t 1) * operator (t 2) * operator (t 3)

lemma quarticProduct_mem_generatedAlgebra (t : Fin 4 → Fin 10) :
    quarticProduct t ∈ generatedAlgebra :=
  generatedAlgebra.mul_mem
    (generatedAlgebra.mul_mem
      (generatedAlgebra.mul_mem (operator_mem_generatedAlgebra _) (operator_mem_generatedAlgebra _))
      (operator_mem_generatedAlgebra _)) (operator_mem_generatedAlgebra _)

/-- The coefficient is the actual bit of the published packed word. -/
theorem quarticProduct_tuple (q : Fin 210) :
    quarticProduct (quarticTuples.get q) = quarticCoefficient q • topOperator := by
  apply matrix_eq_of_operator_commute
  · intro i
    exact (generatedAlgebra_commute (quarticProduct_mem_generatedAlgebra _)
      (operator_mem_generatedAlgebra i)).eq
  · intro i
    apply (generatedAlgebra_commute _ (operator_mem_generatedAlgebra i)).eq
    apply generatedAlgebra.smul_mem
    rw [topOperator_eq_product]
    exact quarticProduct_mem_generatedAlgebra ![0, 1, 2, 3]
  · exact QuarticCertificate.quartic_cyclic q

/-- The exact requested four-operator identity, without an auxiliary product notation. -/
theorem operator_quartic (q : Fin 210) :
    operator (quarticTuples.get q 0) * operator (quarticTuples.get q 1) *
      operator (quarticTuples.get q 2) * operator (quarticTuples.get q 3) =
        quarticCoefficient q • topOperator :=
  quarticProduct_tuple q

lemma quarticProduct_eq_list_prod (t : Fin 4 → Fin 10) :
    quarticProduct t = (List.ofFn (operator ∘ t)).prod := by
  simp [quarticProduct, List.ofFn_succ, mul_assoc]

/-- Every permutation of the four positions preserves the operator product. -/
theorem quarticProduct_comp_perm (t : Fin 4 → Fin 10) (σ : Equiv.Perm (Fin 4)) :
    quarticProduct (t ∘ σ) = quarticProduct t := by
  rw [quarticProduct_eq_list_prod, quarticProduct_eq_list_prod]
  apply List.Perm.prod_eq' (σ.ofFn_comp_perm (operator ∘ t))
  exact List.pairwise_ofFn.mpr fun _ _ _ => operator_mul_comm _ _

private lemma operator_left_comm (i j : Fin 10) (M : SmallMatrix) :
    operator i * (operator j * M) = operator j * (operator i * M) := by
  rw [← mul_assoc, operator_mul_comm i j, mul_assoc]

private lemma operator_twice_mul (i : Fin 10) (M : SmallMatrix) :
    operator i * (operator i * M) = 0 := by
  rw [← mul_assoc, operator_mul_self, zero_mul]

/-- Repeated indices in any two distinct positions force the product to vanish. -/
theorem quarticProduct_eq_zero_of_repeat (t : Fin 4 → Fin 10) (i j : Fin 4)
    (hne : i ≠ j) (h : t i = t j) : quarticProduct t = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [quarticProduct, mul_assoc, operator_left_comm, operator_twice_mul,
      operator_mul_self, operator_mul_comm]

theorem quarticProduct_eq_zero_of_not_injective (t : Fin 4 → Fin 10)
    (h : ¬ Function.Injective t) : quarticProduct t = 0 := by
  classical
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp h
  exact quarticProduct_eq_zero_of_repeat t i j hne heq

/-- This literal entry fixes the scalar normalization of the top line. -/
theorem topOperator_entry_zero_zero : topOperator 0 0 = 1 := by decide +kernel

/-- The scalar coordinate of a fourfold product, using the normalized top entry. -/
def quarticCoordinate (t : Fin 4 → Fin 10) : ZMod 2 := quarticProduct t 0 0

theorem quarticCoordinate_tuple (q : Fin 210) :
    quarticCoordinate (quarticTuples.get q) = quarticCoefficient q := by
  have h := congrArg (fun M : SmallMatrix => M 0 0) (quarticProduct_tuple q)
  simpa only [quarticCoordinate, Matrix.smul_apply, smul_eq_mul,
    topOperator_entry_zero_zero, mul_one] using h

theorem quarticCoordinate_comp_perm (t : Fin 4 → Fin 10) (σ : Equiv.Perm (Fin 4)) :
    quarticCoordinate (t ∘ σ) = quarticCoordinate t :=
  congrArg (fun M : SmallMatrix => M 0 0) (quarticProduct_comp_perm t σ)

theorem quarticCoordinate_eq_zero_of_repeat (t : Fin 4 → Fin 10) (i j : Fin 4)
    (hne : i ≠ j) (h : t i = t j) : quarticCoordinate t = 0 := by
  rw [quarticCoordinate, quarticProduct_eq_zero_of_repeat t i j hne h]
  rfl

/-- Every tuple, including unordered tuples and tuples with repetitions, has
exactly this scalar multiple of the top operator as its product. -/
theorem quarticProduct_eq_coordinate (t : Fin 4 → Fin 10) :
    quarticProduct t = quarticCoordinate t • topOperator := by
  classical
  by_cases ht : Function.Injective t
  · have hs : StrictMono (t ∘ Tuple.sort t) :=
      (Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)
    obtain ⟨q, hq, _⟩ := quarticTuples_existsUnique (t ∘ Tuple.sort t) hs
    have hp : quarticProduct t = quarticCoefficient q • topOperator := by
      rw [← quarticProduct_comp_perm t (Tuple.sort t), ← hq, quarticProduct_tuple]
    have hc : quarticCoordinate t = quarticCoefficient q := by
      rw [← quarticCoordinate_comp_perm t (Tuple.sort t), ← hq, quarticCoordinate_tuple]
    rw [hc]
    exact hp
  · have hz := quarticProduct_eq_zero_of_not_injective t ht
    simp only [quarticCoordinate, hz, Matrix.zero_apply, zero_smul]

/-- Entrywise form of the identity, for use in coordinate constructions. -/
theorem quarticProduct_apply (t : Fin 4 → Fin 10) (i j : Fin 56) :
    quarticProduct t i j = quarticCoordinate t * topOperator i j := by
  rw [quarticProduct_eq_coordinate, Matrix.smul_apply, smul_eq_mul]

/-- The first coordinate of the displayed quartic is one. -/
theorem quarticCoefficient_zero : quarticCoefficient 0 = 1 := by decide +kernel

theorem quarticTuples_zero : quarticTuples.get 0 = ![0, 1, 2, 3] := rfl

theorem quarticCoordinate_zero_one_two_three : quarticCoordinate ![0, 1, 2, 3] = 1 := by
  rw [← quarticTuples_zero, quarticCoordinate_tuple, quarticCoefficient_zero]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
