module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Representative
public import Theory.Mathieu.M24.LocalGeometry.Seed

/-!
# A certified sextet for the six-fixed-point cubic

Each displayed tetrad consists of one fixed point and one orbit of length
three of the native cubic. Fifteen explicit Golay messages certify the
pairwise octad unions. A word in the certified native Mathieu generators
carries the resulting partition to the standard sextet, so the conjugacy
is an actual coordinate identity in M24.

This supplies the geometric object in Aschbacher–Smith H.15.7(1), printed
pp.401–402. Containment of the whole normalizer and the complement to the
intrinsic two-core remain separate group-theoretic assertions.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.SixPoint
open scoped Pointwise

/-- The six tetrads associated to the chosen native cubic. -/
def cubicTetrad : Fin 6 → Finset (Fin 24)
  | 0 => {1,4,6,11}
  | 1 => {2,8,14,21}
  | 2 => {3,9,15,20}
  | 3 => {5,7,10,18}
  | 4 => {12,13,16,17}
  | 5 => {0,19,22,23}

private def cubicTetradMessage : Fin 6 → Fin 4096 := ![0,1366,1626,1266,3154,1107]

private theorem cubicTetrad_union_word (i j : Fin 6) (hij : i ≠ j) :
    cubicTetrad i ∪ cubicTetrad j =
      m24GolayWord (m24GolayMessageXor (cubicTetradMessage i) (cubicTetradMessage j)) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel

theorem cubicTetrad_card (i : Fin 6) : (cubicTetrad i).card = 4 := by
  fin_cases i <;> decide +kernel

theorem cubicTetrad_disjoint (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (cubicTetrad i) (cubicTetrad j) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel

theorem cubicTetrad_union_mem (i j : Fin 6) (hij : i ≠ j) :
    cubicTetrad i ∪ cubicTetrad j ∈ m24Blocks := by
  have hc : (cubicTetrad i ∪ cubicTetrad j).card = 8 := by
    rw [Finset.card_union_of_disjoint (cubicTetrad_disjoint i j hij),
      cubicTetrad_card, cubicTetrad_card]
  rw [cubicTetrad_union_word i j hij] at hc ⊢
  exact m24GolayWord_mem_blocks_of_card_eq_eight _ hc

/-- An actual sextet of the native Witt design, with every octad union checked. -/
def cubicSextet : Sextet where
  parts := Finset.univ.image cubicTetrad
  card := by decide +kernel
  tetrad A hA := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    exact cubicTetrad_card i
  disjoint A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact cubicTetrad_disjoint i j (fun he => hne (congrArg cubicTetrad he))
  cover := by decide +kernel
  octad A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact cubicTetrad_union_mem i j (fun he => hne (congrArg cubicTetrad he))

/-- The cubic acts within each tetrad. -/
theorem cubicRepresentative_tetrad (i : Fin 6) :
    cubicRepresentative.val • cubicTetrad i = cubicTetrad i := by
  fin_cases i <;> decide +kernel

/-- Each tetrad contains exactly one of the six native fixed points. -/
theorem cubicTetrad_fixed_card (i : Fin 6) :
    ((cubicTetrad i).filter fun x => m24Element3B x = x).card = 1 := by
  fin_cases i <;> decide +kernel

theorem cubicSubgroup_le_sextetStabilizer : cubicSubgroup ≤ sextetStabilizer cubicSextet := by
  apply Subgroup.zpowers_le.mpr
  change cubicRepresentative • cubicSextet.parts = cubicSextet.parts
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.mp hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
    change cubicRepresentative.val • cubicTetrad i ∈ _
    rw [cubicRepresentative_tetrad]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · rw [Finset.card_smul_finset]

/-- A word in the certified native generators transporting this sextet to the standard one. -/
noncomputable def cubicSextetConjugator : M24 :=
  ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩ *
    ⟨m24GeneratorB, m24GeneratorB_mem⟩ *
    ⟨m24GeneratorA, m24GeneratorA_mem⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Conjugacy here is witnessed by the actual native action on the partition. -/
theorem cubicSextet_conjugate_standard :
    cubicSextetConjugator.val • cubicSextet.parts = standardSextet.parts := by
  decide +kernel

end MathieuCode.SixPoint
