module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Grading.Products
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Grading.Action
/-!
# The complete grading of the literal seed algebra

The homogeneous spaces here are exactly the spans of increasing squarefree
operator products published in `IntrinsicAlgebra.Data`. The finite action
certificates show that multiplication by each generator raises the selected
basis degree by one. Induction on support therefore identifies each homogeneous
space with the corresponding part of the already certified independent basis.
This proves independence between degrees, dimensions 1, 10, 34, 10, 1, and
vanishing in every higher degree. Squarefree multiplication and the saved basis
expansions give the multiplicative grading of the entire generated algebra.

The coordinate and mathematical source is described in
`IntrinsicAlgebra/source/README.md`; the finite certificate is documented in
`Multiplication/Grading/source/README.md`. No ambient group identification or
additional rank, spanning, or multiplication hypothesis is used.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate GradingCertificate

/-- The part of the certified independent family in one degree. -/
def homogeneousBasisSpan (d : ℕ) : Submodule (ZMod 2) SmallMatrix :=
  Submodule.span (ZMod 2) (gradedBasis '' {j | (basisSet j).card = d})

lemma operator_mul_mem_homogeneousBasisSpan (i : Fin 10) {d : ℕ} {A : SmallMatrix}
    (hA : A ∈ homogeneousBasisSpan d) :
    operator i * A ∈ homogeneousBasisSpan (d + 1) := by
  induction hA using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    rw [operator_mul_gradedBasis]
    apply Submodule.sum_mem
    intro k _
    by_cases h : ((actionCoordinates.get i).get j).testBit k.val = true
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨k, (actionCoordinates_degree i j k h).trans (congrArg (· + 1) hj), rfl⟩
    · have hz : bit ((actionCoordinates.get i).get j) k.val = 0 := by simp [bit, h]
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hx

lemma operatorMonomial_mem_homogeneousBasisSpan (s : Finset (Fin 10)) :
    operatorMonomial s ∈ homogeneousBasisSpan s.card := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty, operatorMonomial_empty, ← gradedBasis_zero]
    exact Submodule.subset_span ⟨0, rfl, rfl⟩
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, operatorMonomial_insert _ _ hi]
    exact operator_mul_mem_homogeneousBasisSpan i ih

/-- Every squarefree monomial is a combination of the selected monomials of
exactly its own degree. -/
theorem homogeneousSpace_eq_basisSpan (d : ℕ) :
    homogeneousSpace d = homogeneousBasisSpan d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨s, hs, rfl⟩
    rw [← hs]
    exact operatorMonomial_mem_homogeneousBasisSpan s
  · apply Submodule.span_le.mpr
    rintro a ⟨j, hj, rfl⟩
    rw [gradedBasis_eq_monomial, ← hj]
    exact operatorMonomial_mem_homogeneousSpace _

/-- Independence between all degrees, including the zero spaces above degree four. -/
theorem homogeneousSpace_iSupIndep : iSupIndep homogeneousSpace := by
  rw [iSupIndep_def]
  intro d
  simp only [homogeneousSpace_eq_basisSpan]
  apply (gradedBasis_linearIndependent.disjoint_span_image
    (s := {j | (basisSet j).card = d}) (t := {j | (basisSet j).card ≠ d})
    (by exact Set.disjoint_left.mpr fun _ h hn => hn h)).mono_right
  apply iSup_le
  intro e
  apply iSup_le
  intro he
  apply Submodule.span_mono
  rintro a ⟨j, hj, rfl⟩
  exact ⟨j, fun h => he (hj.symm.trans h), rfl⟩

lemma homogeneousSpace_finrank_eq_card (d : ℕ) :
    Module.finrank (ZMod 2) (homogeneousSpace d) =
      Fintype.card {j : Fin 56 // (basisSet j).card = d} := by
  rw [homogeneousSpace_eq_basisSpan, homogeneousBasisSpan, Set.image_eq_range]
  exact finrank_span_eq_card
    (gradedBasis_linearIndependent.comp _ Subtype.val_injective)

set_option maxRecDepth 100000 in
theorem homogeneousSpace_finrank_zero : Module.finrank (ZMod 2) (homogeneousSpace 0) = 1 := by
  rw [homogeneousSpace_finrank_eq_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem homogeneousSpace_finrank_one : Module.finrank (ZMod 2) (homogeneousSpace 1) = 10 := by
  rw [homogeneousSpace_finrank_eq_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem homogeneousSpace_finrank_two : Module.finrank (ZMod 2) (homogeneousSpace 2) = 34 := by
  rw [homogeneousSpace_finrank_eq_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem homogeneousSpace_finrank_three : Module.finrank (ZMod 2) (homogeneousSpace 3) = 10 := by
  rw [homogeneousSpace_finrank_eq_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem homogeneousSpace_finrank_four : Module.finrank (ZMod 2) (homogeneousSpace 4) = 1 := by
  rw [homogeneousSpace_finrank_eq_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem homogeneousSpace_eq_bot {d : ℕ} (hd : 5 ≤ d) : homogeneousSpace d = ⊥ := by
  have h : ∀ j : Fin 56, (basisSet j).card ≤ 4 := by decide +kernel
  rw [homogeneousSpace_eq_basisSpan]
  apply Submodule.span_eq_bot.mpr
  rintro a ⟨j, hj, rfl⟩
  have := h j
  change (basisSet j).card = d at hj
  omega

set_option maxRecDepth 100000 in
theorem homogeneousSpace_four : homogeneousSpace 4 = Submodule.span (ZMod 2) {topOperator} := by
  have h : ∀ j : Fin 56, (basisSet j).card = 4 ↔ j = 55 := by decide +kernel
  rw [homogeneousSpace_eq_basisSpan, homogeneousBasisSpan, topOperator_eq_gradedBasis]
  apply congrArg (Submodule.span (ZMod 2))
  ext a
  simp only [Set.mem_image, Set.mem_ofPred, Set.mem_singleton_iff, h]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨55, rfl, rfl⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
