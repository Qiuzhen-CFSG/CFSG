module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.SubgroupClosureWords
public import Theory.GroupTheory.SubgroupEnumerationBinary
import Mathlib.Tactic.FinCases

/-!
# Upper maximal steps in the Ree two parity census

Every maximal subgroup of nodes 0–28 outside the parity kernel is conjugate
to a node in the same fixed census. No centricity or Frattini pruning is needed
for these upper nodes.

Minimal generating families are certified against the original displayed
families by positive words in both directions. For the actual membership
signature of a maximal subgroup, the first outside generator gives an index-two
Schreier transversal. We check that pivot for every nonzero signature: the 191
branches comprise 29 parity containments and 162 conjugacies. The conjugacies
are also certified by words in both directions. In particular, a table checking
one pivot is never treated as checking all pivots.

Source: Shinoda (1975), (2.3), pp. 81–82, in the verified `ReeTwo.Sylow` model;
the fixed root words in `SmallParityCensusNodes`; Schreier's lemma in
`SubgroupEnumerationBinary`. The exploratory GAP certificates select words and
conjugators only. Every finite equation below is checked by the Lean kernel.
The convention for a conjugator g is g * edge * g⁻¹ = target.
-/

set_option maxRecDepth 2048
namespace ReeTwo.SylowModel
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

private theorem closure_eq_words {n m : ℕ} (s : Fin n → SylowModel)
    (t : Fin m → SylowModel) (w : Fin n → List (Fin m))
    (v : Fin m → List (Fin n))
    (hw : ∀ i, evalWord t (w i) = s i)
    (hv : ∀ i, evalWord s (v i) = t i) :
    Subgroup.closure (Set.range s) = Subgroup.closure (Set.range t) := by
  simpa using (ClosureWords.sound ⟨w,v⟩ s t (MonoidHom.id _) ⟨hw,hv⟩)

private theorem chosen_binary {n : ℕ} (i : Fin 131) (s : Fin n → SylowModel)
    (hs : Subgroup.closure (Set.range s) = smallParityCensusNode i)
    (hc : ∀ σ : Fin n → Bool, (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator s (s j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L)
    (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode i)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  classical
  let σ : Fin n → Bool := fun j => decide (s j ∉ H)
  have hσ : ∀ j, σ j = true ↔ s j ∉ H := fun j => by simp [σ]
  rcases hc σ with hz | ⟨j, hj, hc⟩
  · have hle : smallParityCensusNode i ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      simpa [σ] using hz j
    exact (hm.lt.not_ge hle).elim
  · have he := binarySchreier_eq_relative hm.le
      (relIndex_two_of_covBy (IsPGroup.of_card (p := 2) (n := 12) card) hm)
      s hs (s j) (hs ▸ Subgroup.subset_closure ⟨j, rfl⟩) ((hσ j).mp hj) σ hσ
    dsimp only at hc
    rw [he] at hc
    exact hc.resolve_left hp

private theorem top_of_roots (H : Subgroup SylowModel)
    (h1 : rootOne ∈ H) (hr : ∀ i, root i ∈ H) : H = ⊤ := by
  apply top_unique
  intro x _
  have hl : SemidirectProduct.inl x.left ∈ H := by
    rw [← Core.normal_form x.left]
    simp only [map_mul, map_pow]
    repeat first | apply H.mul_mem | exact H.pow_mem (hr _) _
  have ht : SemidirectProduct.inr x.right ∈ H := by
    rw [← FiveFour.generator_pow_val x.right, map_pow]
    apply H.pow_mem
    exact H.inv_mem_iff.mp (show (SemidirectProduct.inr (FiveFour.generator 4) : SylowModel)⁻¹ ∈ H from h1)
  simpa only [SemidirectProduct.inl_left_mul_inr_right] using H.mul_mem hl ht

private def flatSchreier {n : ℕ} (s : Fin n → SylowModel) (j : Fin n)
    (σ : Fin n → Bool) : Fin (n+n) → SylowModel :=
  Fin.addCases (fun k => binarySchreierGenerator s (s j) σ (false,k))
    (fun k => binarySchreierGenerator s (s j) σ (true,k))

private theorem flat_range {n : ℕ} (s : Fin n → SylowModel) (j : Fin n)
    (σ : Fin n → Bool) : Set.range (flatSchreier s j σ) =
      Set.range (binarySchreierGenerator s (s j) σ) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left k => exact ⟨(false,k), by simp only [flatSchreier, Fin.addCases_left]⟩
    | right k => exact ⟨(true,k), by simp only [flatSchreier, Fin.addCases_right]⟩
  · rintro ⟨⟨b,k⟩, rfl⟩
    cases b
    · exact ⟨Fin.castAdd n k, by simp only [flatSchreier, Fin.addCases_left]⟩
    · exact ⟨Fin.natAdd n k, by simp only [flatSchreier, Fin.addCases_right]⟩



private def original0 : Fin 12 → SylowModel := ![rootOne, rootOne ^ 2, root 0, root 1, root 2, root 3, root 4, root 5, root 6, root 7, root 8, root 9]

private theorem original0_eq : Subgroup.closure (Set.range original0) = smallParityCensusNode 0 := by
  rw [smallParityCensusNode_zero]
  apply top_of_roots
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · intro i
    fin_cases i <;> apply Subgroup.subset_closure
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩

private def original1 : Fin 11 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original1_eq : Subgroup.closure (Set.range original1) = smallParityCensusNode 1 := by
  change Subgroup.closure (Set.range ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original2 : Fin 11 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original2_eq : Subgroup.closure (Set.range original2) = smallParityCensusNode 2 := by
  change Subgroup.closure (Set.range ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original3 : Fin 11 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original3_eq : Subgroup.closure (Set.range original3) = smallParityCensusNode 3 := by
  change Subgroup.closure (Set.range ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original4 : Fin 11 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original4_eq : Subgroup.closure (Set.range original4) = smallParityCensusNode 4 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original5 : Fin 11 → SylowModel := ![root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original5_eq : Subgroup.closure (Set.range original5) = smallParityCensusNode 5 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original6 : Fin 11 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original6_eq : Subgroup.closure (Set.range original6) = smallParityCensusNode 6 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original7 : Fin 10 → SylowModel := ![rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original7_eq : Subgroup.closure (Set.range original7) = smallParityCensusNode 7 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne ^ 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original8 : Fin 10 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original8_eq : Subgroup.closure (Set.range original8) = smallParityCensusNode 8 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original9 : Fin 10 → SylowModel := ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original9_eq : Subgroup.closure (Set.range original9) = smallParityCensusNode 9 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original10 : Fin 10 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]

private theorem original10_eq : Subgroup.closure (Set.range original10) = smallParityCensusNode 10 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original11 : Fin 10 → SylowModel := ![root 3, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]

private theorem original11_eq : Subgroup.closure (Set.range original11) = smallParityCensusNode 11 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]) = Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original12 : Fin 10 → SylowModel := ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]

private theorem original12_eq : Subgroup.closure (Set.range original12) = smallParityCensusNode 12 := by
  change Subgroup.closure (Set.range ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]) = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original13 : Fin 10 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]

private theorem original13_eq : Subgroup.closure (Set.range original13) = smallParityCensusNode 13 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original14 : Fin 10 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]

private theorem original14_eq : Subgroup.closure (Set.range original14) = smallParityCensusNode 14 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original15 : Fin 9 → SylowModel := ![rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]

private theorem original15_eq : Subgroup.closure (Set.range original15) = smallParityCensusNode 15 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9]) = Subgroup.closure ({rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original16 : Fin 9 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]

private theorem original16_eq : Subgroup.closure (Set.range original16) = smallParityCensusNode 16 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original17 : Fin 9 → SylowModel := ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 5, root 4 * root 9, root 6 * root 8, root 7 * root 8, root 8 * root 9, root 9]

private theorem original17_eq : Subgroup.closure (Set.range original17) = smallParityCensusNode 17 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 5, root 4 * root 9, root 6 * root 8, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 5, root 4 * root 9, root 6 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original18 : Fin 9 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2 * root 4 * root 8, root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, root 4 * root 9, root 6 * root 7 * root 8, root 7 * root 8, root 8, root 9]

private theorem original18_eq : Subgroup.closure (Set.range original18) = smallParityCensusNode 18 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2 * root 4 * root 8, root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, root 4 * root 9, root 6 * root 7 * root 8, root 7 * root 8, root 8, root 9]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, rootOne ^ 2 * root 4 * root 8, root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, root 4 * root 9, root 6 * root 7 * root 8, root 7 * root 8, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original19 : Fin 9 → SylowModel := ![root 3, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original19_eq : Subgroup.closure (Set.range original19) = smallParityCensusNode 19 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original20 : Fin 9 → SylowModel := ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original20_eq : Subgroup.closure (Set.range original20) = smallParityCensusNode 20 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original21 : Fin 9 → SylowModel := ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original21_eq : Subgroup.closure (Set.range original21) = smallParityCensusNode 21 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original22 : Fin 9 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original22_eq : Subgroup.closure (Set.range original22) = smallParityCensusNode 22 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original23 : Fin 9 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original23_eq : Subgroup.closure (Set.range original23) = smallParityCensusNode 23 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original24 : Fin 9 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original24_eq : Subgroup.closure (Set.range original24) = smallParityCensusNode 24 := by
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original25 : Fin 9 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original25_eq : Subgroup.closure (Set.range original25) = smallParityCensusNode 25 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original26 : Fin 9 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original26_eq : Subgroup.closure (Set.range original26) = smallParityCensusNode 26 := by
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original27 : Fin 9 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9]

private theorem original27_eq : Subgroup.closure (Set.range original27) = smallParityCensusNode 27 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original28 : Fin 9 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9]

private theorem original28_eq : Subgroup.closure (Set.range original28) = smallParityCensusNode 28 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original29 : Fin 8 → SylowModel := ![rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original29_eq : Subgroup.closure (Set.range original29) = smallParityCensusNode 29 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original30 : Fin 8 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original30_eq : Subgroup.closure (Set.range original30) = smallParityCensusNode 30 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original31 : Fin 8 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original31_eq : Subgroup.closure (Set.range original31) = smallParityCensusNode 31 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original32 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original32_eq : Subgroup.closure (Set.range original32) = smallParityCensusNode 32 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original33 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]

private theorem original33_eq : Subgroup.closure (Set.range original33) = smallParityCensusNode 33 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original34 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9]

private theorem original34_eq : Subgroup.closure (Set.range original34) = smallParityCensusNode 34 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original35 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]

private theorem original35_eq : Subgroup.closure (Set.range original35) = smallParityCensusNode 35 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original36 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]

private theorem original36_eq : Subgroup.closure (Set.range original36) = smallParityCensusNode 36 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original37 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]

private theorem original37_eq : Subgroup.closure (Set.range original37) = smallParityCensusNode 37 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original38 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]

private theorem original38_eq : Subgroup.closure (Set.range original38) = smallParityCensusNode 38 := by
  change Subgroup.closure (Set.range ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]) = Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original39 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original39_eq : Subgroup.closure (Set.range original39) = smallParityCensusNode 39 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original40 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original40_eq : Subgroup.closure (Set.range original40) = smallParityCensusNode 40 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original41 : Fin 8 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original41_eq : Subgroup.closure (Set.range original41) = smallParityCensusNode 41 := by
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original42 : Fin 8 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original42_eq : Subgroup.closure (Set.range original42) = smallParityCensusNode 42 := by
  change Subgroup.closure (Set.range ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original43 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]

private theorem original43_eq : Subgroup.closure (Set.range original43) = smallParityCensusNode 43 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original44 : Fin 8 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]

private theorem original44_eq : Subgroup.closure (Set.range original44) = smallParityCensusNode 44 := by
  change Subgroup.closure (Set.range ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]) = Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original45 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8]

private theorem original45_eq : Subgroup.closure (Set.range original45) = smallParityCensusNode 45 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original46 : Fin 8 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original46_eq : Subgroup.closure (Set.range original46) = smallParityCensusNode 46 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original47 : Fin 8 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]

private theorem original47_eq : Subgroup.closure (Set.range original47) = smallParityCensusNode 47 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original48 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]

private theorem original48_eq : Subgroup.closure (Set.range original48) = smallParityCensusNode 48 := by
  change Subgroup.closure (Set.range ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]) = Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original49 : Fin 8 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]

private theorem original49_eq : Subgroup.closure (Set.range original49) = smallParityCensusNode 49 := by
  change Subgroup.closure (Set.range ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]) = Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original50 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]

private theorem original50_eq : Subgroup.closure (Set.range original50) = smallParityCensusNode 50 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original51 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original51_eq : Subgroup.closure (Set.range original51) = smallParityCensusNode 51 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original52 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original52_eq : Subgroup.closure (Set.range original52) = smallParityCensusNode 52 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original53 : Fin 8 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original53_eq : Subgroup.closure (Set.range original53) = smallParityCensusNode 53 := by
  change Subgroup.closure (Set.range ![root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original54 : Fin 8 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original54_eq : Subgroup.closure (Set.range original54) = smallParityCensusNode 54 := by
  change Subgroup.closure (Set.range ![root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original55 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original55_eq : Subgroup.closure (Set.range original55) = smallParityCensusNode 55 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original56 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original56_eq : Subgroup.closure (Set.range original56) = smallParityCensusNode 56 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original57 : Fin 8 → SylowModel := ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original57_eq : Subgroup.closure (Set.range original57) = smallParityCensusNode 57 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original58 : Fin 8 → SylowModel := ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]

private theorem original58_eq : Subgroup.closure (Set.range original58) = smallParityCensusNode 58 := by
  change Subgroup.closure (Set.range ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]) = Subgroup.closure ({root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original59 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]

private theorem original59_eq : Subgroup.closure (Set.range original59) = smallParityCensusNode 59 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def original60 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]

private theorem original60_eq : Subgroup.closure (Set.range original60) = smallParityCensusNode 60 := by
  change Subgroup.closure (Set.range ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]) = Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private def gen0 : Fin 3 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 3]

private theorem gen0_eq : Subgroup.closure (Set.range gen0) = smallParityCensusNode 0 := by
  rw [← original0_eq]
  exact closure_eq_words gen0 original0
    (![[2, 1], [1, 2, 5], [0, 1]])
    (![[2, 2, 2], [2, 2], [0, 2, 2], [0, 1, 2, 0, 2, 0, 1, 1, 2, 2], [1, 1, 2, 0, 1, 2, 2, 2], [0, 1], [0, 0, 0, 2, 1, 0, 2, 1, 2, 2], [2, 0, 1, 1, 0, 2, 2, 2], [0, 0, 2, 0, 2, 2, 1, 2, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 1, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 0 (![true, false, false])]

  right
  refine ⟨3, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original3_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 0 (![true, false, false]))) original3
    (![[], [0], [1], [4], [4, 0, 5], [3, 5, 1]])
    (![[1], [2], [2, 2], [2, 5, 2, 2], [3], [1, 1, 1, 3, 4], [1, 2, 5, 5, 2, 4], [1, 1, 5, 2, 5, 3, 2], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 1 (![false, true, false])]

  right
  refine ⟨1, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original1_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 1 (![false, true, false]))) original1
    (![[0], [], [1], [4, 5, 0, 10], [5, 8], [1, 3, 6, 7]])
    (![[0], [2], [2, 2], [2, 0, 2, 0, 5, 5], [0, 0], [0, 4, 3, 4], [5, 2, 2, 5, 0, 0], [0, 5, 0, 2, 5, 5], [0, 4, 3], [3, 4, 0], [0, 0, 3, 4, 3, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 0 (![true, true, false])]

  right
  refine ⟨5, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original5_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 0 (![true, true, false]))) original5
    (![[], [0, 5], [1], [4], [0], [3, 5, 1]])
    (![[4], [2], [2, 2], [2, 5, 2, 2], [3], [4, 1, 4, 4], [5, 4, 5, 4, 5, 5], [1, 2, 3, 5, 1, 5, 2], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 2 (![false, false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen0 2 (![false, false, true])) k ∈ character.ker) k

private theorem edge0_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 0 (![true, false, true])]

  right
  refine ⟨4, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original4_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 0 (![true, false, true]))) original4
    (![[], [1], [2, 0, 3, 2], [4], [4, 1, 5], [0]])
    (![[5], [1], [2, 5], [2, 3, 2, 2, 5], [3], [1, 1, 1, 3, 4], [2, 2, 1, 4, 5, 5], [4, 5, 1, 2, 2, 2], [1, 3, 4], [1, 4, 3], [1, 1, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 1 (![false, true, true])]

  right
  refine ⟨2, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original2_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 1 (![false, true, true]))) original2
    (![[0], [], [1, 3, 5, 9], [4, 5, 0, 10], [5, 8], [1]])
    (![[0], [5], [2, 5], [2, 5, 2, 2, 4], [0, 0], [0, 4, 3, 4], [5, 5, 2, 2, 0, 0], [5, 5, 0, 5, 5, 0], [0, 4, 3], [3, 4, 0], [0, 0, 3, 4, 3, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge0_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen0 0 (![true, true, true])]

  right
  refine ⟨6, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original6_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen0 0 (![true, true, true]))) original6
    (![[], [1, 0, 3, 2], [2, 0, 3, 2], [4], [0, 2, 1, 3], [0]])
    (![[5], [1, 5], [2, 5], [2, 3, 2, 2, 5], [3], [4, 1, 4, 4], [1, 2, 5, 5, 3, 2, 1], [4, 2, 4, 2, 2, 2], [1, 1, 3, 3], [1, 1], [1, 1, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks0 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen0 (gen0 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge0_1⟩

  · exact Or.inr ⟨1, by decide, edge0_2⟩

  · exact Or.inr ⟨0, by decide, edge0_3⟩

  · exact Or.inr ⟨2, by decide, edge0_4⟩

  · exact Or.inr ⟨0, by decide, edge0_5⟩

  · exact Or.inr ⟨1, by decide, edge0_6⟩

  · exact Or.inr ⟨0, by decide, edge0_7⟩

private theorem step0 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 0)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 0 gen0 gen0_eq checks0 H hm hp

private def gen1 : Fin 2 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3]

private theorem gen1_eq : Subgroup.closure (Set.range gen1) = smallParityCensusNode 1 := by
  rw [← original1_eq]
  exact closure_eq_words gen1 original1
    (![[0], [1]])
    (![[0], [1], [1, 1], [1, 0, 1, 1, 1, 0], [0, 0], [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1], [1, 0, 0, 0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge1_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen1 (gen1 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen1 0 (![true, false])]

  right
  refine ⟨7, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original7_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen1 0 (![true, false]))) original7
    (![[], [0], [3], [2, 4, 0]])
    (![[1], [1, 1], [1, 3, 1, 1], [2], [3, 2, 1, 3, 1], [1, 2, 3, 2, 3, 2, 1], [3, 2, 1, 2, 1, 3, 2], [3, 1, 1, 2, 3], [1, 1, 2, 3, 2, 2, 3], [1, 3, 1, 3, 1, 3, 1, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge1_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen1 (gen1 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen1 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen1 1 (![false, true])) k ∈ character.ker) k

private theorem edge1_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen1 (gen1 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen1 0 (![true, true])]

  right
  refine ⟨8, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original8_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen1 0 (![true, true]))) original8
    (![[], [1, 0, 2, 1], [3], [0]])
    (![[3], [1, 3], [1, 2, 1, 1, 3], [2], [1, 1, 1, 2, 1, 2, 2], [1, 1, 2, 3, 2, 2, 3], [3, 2, 1, 1, 2, 3, 2], [3, 2, 3, 1, 1], [1, 1, 2, 2, 3, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks1 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen1 (gen1 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge1_1⟩

  · exact Or.inr ⟨1, by decide, edge1_2⟩

  · exact Or.inr ⟨0, by decide, edge1_3⟩

private theorem step1 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 1)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 1 gen1 gen1_eq checks1 H hm hp

private def gen2 : Fin 2 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen2_eq : Subgroup.closure (Set.range gen2) = smallParityCensusNode 2 := by
  rw [← original2_eq]
  exact closure_eq_words gen2 original2
    (![[0], [1]])
    (![[0], [1], [1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0, 1, 0, 0], [0, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1, 1, 0, 0], [1, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge2_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen2 (gen2 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen2 0 (![true, false])]

  right
  refine ⟨9, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original9_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen2 0 (![true, false]))) original9
    (![[], [0], [3], [2, 6, 0, 4]])
    (![[1], [1, 1, 2, 3, 1, 3, 2, 3], [2, 1, 1, 3, 2, 1, 2], [2], [3, 3, 3, 2, 3], [2, 1, 3, 1, 2, 3], [1, 1, 3, 3, 2], [1, 2, 3, 3, 1], [3, 1, 3, 1], [1, 1, 2, 3, 3, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge2_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen2 (gen2 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen2 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen2 1 (![false, true])) k ∈ character.ker) k

private theorem edge2_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen2 (gen2 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen2 0 (![true, true])]

  right
  refine ⟨10, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original10_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen2 0 (![true, true]))) original10
    (![[], [2, 0, 6], [3], [0]])
    (![[3], [1, 1, 1, 2, 1, 3, 3, 2], [2, 1, 1, 1, 3], [2], [3, 1, 3, 2, 1], [3, 2, 1, 2, 1, 3, 2], [1, 3, 3, 1, 2], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1], [1, 2, 2, 1, 3, 2, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem checks2 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen2 (gen2 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge2_1⟩

  · exact Or.inr ⟨1, by decide, edge2_2⟩

  · exact Or.inr ⟨0, by decide, edge2_3⟩

private theorem step2 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 2)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 2 gen2 gen2_eq checks2 H hm hp

private def gen3 : Fin 2 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 3]

private theorem gen3_eq : Subgroup.closure (Set.range gen3) = smallParityCensusNode 3 := by
  rw [← original3_eq]
  exact closure_eq_words gen3 original3
    (![[0], [1]])
    (![[0], [1], [1, 1], [0, 0, 0, 1, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1], [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge3_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen3 (gen3 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen3 0 (![true, false])]

  right
  refine ⟨7, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original7_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen3 0 (![true, false]))) original7
    (![[], [0], [4, 7], [0, 2, 5, 6]])
    (![[1], [1, 1], [1, 2, 1, 2, 2, 3, 1], [1, 1, 3, 3], [2, 3, 2, 2, 3, 3, 3], [3, 1, 1, 3, 1, 1, 3, 3], [1, 1, 3, 1, 3, 3, 1, 3], [3, 2, 2, 3, 3, 3], [2, 2, 3, 2, 2, 3, 3, 3], [1, 3, 1, 3, 1, 3, 1, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge3_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen3 (gen3 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen3 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen3 1 (![false, true])) k ∈ character.ker) k

private theorem edge3_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen3 (gen3 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen3 0 (![true, true])]

  right
  refine ⟨9, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original9_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen3 0 (![true, true]))) original9
    (![[], [0, 2, 4, 8], [4, 7], [0]])
    (![[3], [1, 3], [1, 3, 1, 1, 2], [1, 3, 3, 1], [2, 3, 1, 3, 2, 2, 1], [3, 3, 1, 1, 1, 3, 3, 1], [1, 1, 3, 3, 3, 3, 2, 3, 3], [3, 1, 3, 2, 2, 1], [2, 2, 3, 1, 3, 2, 2, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks3 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen3 (gen3 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge3_1⟩

  · exact Or.inr ⟨1, by decide, edge3_2⟩

  · exact Or.inr ⟨0, by decide, edge3_3⟩

private theorem step3 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 3)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 3 gen3 gen3_eq checks3 H hm hp

private def gen4 : Fin 2 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9]

private theorem gen4_eq : Subgroup.closure (Set.range gen4) = smallParityCensusNode 4 := by
  rw [← original4_eq]
  exact closure_eq_words gen4 original4
    (![[1], [0]])
    (![[1], [0], [0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1], [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1], [0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 1, 0], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge4_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen4 (gen4 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen4 0 (![true, false])]

  right
  refine ⟨8, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original8_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen4 0 (![true, false]))) original8
    (![[], [0], [4, 7], [2, 5, 4, 0]])
    (![[1], [3, 3, 2, 2, 3, 3, 1, 3], [1, 2, 3, 2, 3, 2, 3], [3, 2, 3, 3, 2, 2, 3], [1, 3, 2, 1, 3], [2, 3, 2, 1, 3, 1], [1, 1, 1, 1, 3, 3, 3, 3], [3, 1, 3, 1], [1, 2, 3, 1, 2, 3], [1, 3, 1, 3, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge4_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen4 (gen4 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen4 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen4 1 (![false, true])) k ∈ character.ker) k

private theorem edge4_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen4 (gen4 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen4 0 (![true, true])]

  right
  refine ⟨10, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original10_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen4 0 (![true, true]))) original10
    (![[], [0, 2, 4, 8], [4, 7], [0, 2, 7, 2]])
    (![[3, 2, 3, 1, 1, 3], [1, 3, 2, 1, 1, 1, 3], [2, 1, 1, 1, 3], [3, 2, 1, 3, 2, 2, 1], [1, 1, 1, 1, 2, 2, 2], [1, 1, 1, 3, 3, 1, 3, 3], [1, 3, 1, 3, 3, 1, 3, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem checks4 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen4 (gen4 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge4_1⟩

  · exact Or.inr ⟨1, by decide, edge4_2⟩

  · exact Or.inr ⟨0, by decide, edge4_3⟩

private theorem step4 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 4)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 4 gen4 gen4_eq checks4 H hm hp

private def gen5 : Fin 3 → SylowModel := ![rootOne ^ 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 3]

private theorem gen5_eq : Subgroup.closure (Set.range gen5) = smallParityCensusNode 5 := by
  rw [← original5_eq]
  exact closure_eq_words gen5 original5
    (![[1], [3], [0]])
    (![[2], [0], [0, 0], [1], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1], [0, 1, 0, 2, 0, 2, 1, 0, 1, 1], [1, 0, 0, 1, 1, 0, 0, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 1, 2, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 0 (![true, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen5 0 (![true, false, false])) k ∈ character.ker) k

private theorem edge5_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 1 (![false, true, false])]

  right
  refine ⟨11, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original11_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen5 1 (![false, true, false]))) original11
    (![[1], [], [0], [4, 1, 5, 6], [3], [0, 9]])
    (![[2], [0], [0, 0], [4], [0, 3, 4, 0, 4, 0], [0, 0, 4, 3, 3, 4], [0, 0, 0, 4, 0, 4], [0, 0, 4, 0, 0, 4], [2, 2], [2, 2, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 0 (![true, true, false])]

  right
  refine ⟨11, rootOne ^ 2 * root 0 * root 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original11_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 2 * root 0 * root 3)).toMonoidHom ∘ (flatSchreier gen5 0 (![true, true, false]))) original11
    (![[], [2, 3, 1, 9], [0, 3, 6], [3, 6, 2, 4], [1], [0, 3, 5, 7]])
    (![[4, 1, 2], [4], [4, 4], [3, 1, 4, 3], [1, 1, 3, 1, 4], [1, 1, 4, 2, 4, 2], [4, 4, 1, 1], [1, 1, 5, 1, 1, 5], [1, 1, 1, 1], [1, 1, 1, 1, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 2 (![false, false, true])]

  right
  refine ⟨7, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original7_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen5 2 (![false, false, true]))) original7
    (![[0], [2], [], [0, 5, 7], [2, 9], [8, 9]])
    (![[0], [0, 0], [1], [0, 0, 0, 1, 0, 1], [0, 0, 1, 1, 1, 3, 4, 0], [0, 0, 1, 1, 0, 3, 1, 1], [0, 0, 1, 0, 1, 1, 3, 4], [0, 0, 1, 0, 3, 1, 1, 1], [1, 1, 1, 4, 5], [1, 1, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 0 (![true, false, true])]

  right
  refine ⟨10, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original10_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen5 0 (![true, false, true]))) original10
    (![[], [2], [0, 1], [1], [1, 2, 1, 4], [0, 5, 7]])
    (![[2, 3], [3], [1], [3, 4, 3, 1], [1, 1, 1, 3, 4, 3], [1, 2, 1, 5, 1, 4], [1, 1, 4, 5, 1, 2], [4, 1, 4, 1], [1, 1, 1, 2, 4, 5], [1, 3, 4, 5, 4, 5, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 1 (![false, true, true])]

  right
  refine ⟨12, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original12_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen5 1 (![false, true, true]))) original12
    (![[1], [], [0, 3], [4, 1, 5, 6], [3], [0, 9]])
    (![[2, 4], [0], [0, 0], [4], [0, 2, 0, 5, 3, 3], [0, 0, 4, 3, 3, 4], [0, 0, 0, 4, 0, 4], [0, 0, 4, 0, 0, 4], [2, 5], [2, 2, 2, 4, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge5_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen5 0 (![true, true, true])]

  right
  refine ⟨12, rootOne ^ 2 * root 0 * root 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original12_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 2 * root 0 * root 3)).toMonoidHom ∘ (flatSchreier gen5 0 (![true, true, true]))) original12
    (![[], [2, 3, 1, 9], [2, 0, 1], [3, 6, 2, 4], [1], [1, 5, 0, 3]])
    (![[4, 1, 4, 5, 1, 1], [4], [4, 4], [3, 1, 4, 3], [1, 1, 3, 1, 4], [1, 1, 2, 1, 1, 5], [4, 4, 1, 1], [1, 3, 4, 1, 3, 4], [1, 1, 1, 1], [1, 1, 1, 1, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem checks5 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen5 (gen5 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge5_1⟩

  · exact Or.inr ⟨1, by decide, edge5_2⟩

  · exact Or.inr ⟨0, by decide, edge5_3⟩

  · exact Or.inr ⟨2, by decide, edge5_4⟩

  · exact Or.inr ⟨0, by decide, edge5_5⟩

  · exact Or.inr ⟨1, by decide, edge5_6⟩

  · exact Or.inr ⟨0, by decide, edge5_7⟩

private theorem step5 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 5)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 5 gen5 gen5_eq checks5 H hm hp

private def gen6 : Fin 3 → SylowModel := ![root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen6_eq : Subgroup.closure (Set.range gen6) = smallParityCensusNode 6 := by
  rw [← original6_eq]
  exact closure_eq_words gen6 original6
    (![[3], [0], [1]])
    (![[1], [2], [1, 1, 0], [0], [0, 2, 1, 2, 0, 1], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 1, 1, 1, 1], [0, 0, 1, 1, 0, 2, 2, 0], [0, 1, 2, 0, 1, 2], [0, 2, 1, 0, 2, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 0 (![true, false, false])]

  right
  refine ⟨13, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original13_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen6 0 (![true, false, false]))) original13
    (![[], [0], [1], [2, 5, 2], [0, 4, 3, 6], [1, 3, 4, 7]])
    (![[1], [2], [1, 1], [1, 4, 1, 1], [1, 1, 1, 1], [4, 2, 5, 1], [2, 5, 4, 1], [1, 1, 3, 4, 4], [2, 1, 5, 4, 3], [1, 2, 3, 4, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 1 (![false, true, false])]

  right
  refine ⟨9, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original9_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen6 1 (![false, true, false]))) original9
    (![[2], [], [0], [0, 1, 0, 8], [1, 2, 2, 2], [0, 2, 2]])
    (![[2], [4, 0], [0], [3, 0, 3, 3], [3, 2, 3, 2, 4], [0, 0, 4, 4], [2, 3, 4, 5, 0], [0, 5, 3, 4, 2], [0, 2, 3, 5, 4], [4, 4, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 0 (![true, true, false])]

  right
  refine ⟨14, rootOne ^ 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original14_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 3)).toMonoidHom ∘ (flatSchreier gen6 0 (![true, true, false]))) original14
    (![[], [3, 0, 6], [1], [0, 5, 0, 2, 9], [5, 0], [3, 1, 4]])
    (![[4, 5, 5, 4, 1], [2], [1, 2, 1, 2, 5, 2], [2, 2, 5, 2], [2, 2, 1, 4, 3], [5, 4, 1, 5], [5, 1, 4, 5], [2, 1, 2, 1], [5, 4, 5, 4], [1, 5, 1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 2 (![false, false, true])]

  right
  refine ⟨8, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original8_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen6 2 (![false, false, true]))) original8
    (![[2], [0], [], [3, 2, 9], [0, 2, 2, 9], [1, 6, 2]])
    (![[1], [1, 1, 0], [0], [0, 0, 3, 0], [0, 3], [1, 1, 1, 4], [3, 5, 4, 0, 1], [5, 3, 5, 3], [0, 4, 3, 5, 1], [5, 5, 5, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 0 (![true, false, true])]

  right
  refine ⟨14, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original14_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen6 0 (![true, false, true]))) original14
    (![[], [0], [1, 2, 5, 2], [2, 5, 2], [0, 4, 3, 6], [1, 4, 6, 3]])
    (![[1], [2, 3], [1, 1], [1, 4, 1, 1], [1, 1, 1, 1], [5, 1, 1, 2], [5, 4, 4, 2], [1, 1, 3, 4, 4], [5, 1, 5, 1], [1, 2, 1, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge6_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 1 (![false, true, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen6 1 (![false, true, true])) k ∈ character.ker) k

private theorem edge6_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen6 0 (![true, true, true])]

  right
  refine ⟨13, rootOne ^ 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original13_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 3)).toMonoidHom ∘ (flatSchreier gen6 0 (![true, true, true]))) original13
    (![[], [3, 0, 6], [6, 3, 1], [2, 1, 4, 1], [5, 0], [1, 5, 9]])
    (![[4, 4, 4, 5, 5], [4, 1, 5, 2, 5], [1, 2, 4, 1, 5, 1], [4, 4, 2, 5], [2, 2, 2, 2], [5, 1, 4, 2], [1, 5, 5, 1], [2, 4, 3, 5, 1], [2, 2, 5, 3, 5], [1, 5, 3, 4, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks6 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen6 (gen6 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge6_1⟩

  · exact Or.inr ⟨1, by decide, edge6_2⟩

  · exact Or.inr ⟨0, by decide, edge6_3⟩

  · exact Or.inr ⟨2, by decide, edge6_4⟩

  · exact Or.inr ⟨0, by decide, edge6_5⟩

  · exact Or.inr ⟨1, by decide, edge6_6⟩

  · exact Or.inr ⟨0, by decide, edge6_7⟩

private theorem step6 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 6)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 6 gen6 gen6_eq checks6 H hm hp

private def gen7 : Fin 2 → SylowModel := ![rootOne ^ 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9]

private theorem gen7_eq : Subgroup.closure (Set.range gen7) = smallParityCensusNode 7 := by
  rw [← original7_eq]
  exact closure_eq_words gen7 original7
    (![[0], [2]])
    (![[0], [0, 0], [1], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge7_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen7 (gen7 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen7 0 (![true, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen7 0 (![true, false])) k ∈ character.ker) k

private theorem edge7_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen7 (gen7 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen7 1 (![false, true])]

  right
  refine ⟨15, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original15_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen7 1 (![false, true]))) original15
    (![[0], [], [3, 0, 4, 5], [2]])
    (![[0], [0, 0], [3], [0, 2, 3, 0, 3, 0], [0, 0, 3, 2, 2, 3], [0, 0, 0, 3, 0, 3], [0, 0, 3, 0, 0, 3], [0, 0, 2, 0, 0, 2, 2, 2], [0, 0, 0, 2, 0, 2, 3, 0, 0, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge7_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen7 (gen7 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen7 0 (![true, true])]

  right
  refine ⟨15, rootOne ^ 2 * root 0 * root 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original15_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 2 * root 0 * root 3)).toMonoidHom ∘ (flatSchreier gen7 0 (![true, true]))) original15
    (![[], [1, 2, 0, 8], [2, 5, 1, 3], [0]])
    (![[3], [3, 3], [2, 1, 3, 2], [1, 1, 2, 1, 3], [1, 3, 2, 3, 2, 1], [3, 3, 1, 1], [1, 2, 3, 1, 2, 3], [1, 1, 1, 1], [1, 2, 3, 2, 1, 2, 3, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks7 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen7 (gen7 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge7_1⟩

  · exact Or.inr ⟨1, by decide, edge7_2⟩

  · exact Or.inr ⟨0, by decide, edge7_3⟩

private theorem step7 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 7)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 7 gen7 gen7_eq checks7 H hm hp

private def gen8 : Fin 2 → SylowModel := ![root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9]

private theorem gen8_eq : Subgroup.closure (Set.range gen8) = smallParityCensusNode 8 := by
  rw [← original8_eq]
  exact closure_eq_words gen8 original8
    (![[2], [0]])
    (![[1], [1, 1, 0], [0], [1, 1, 1, 0, 1, 0], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 1, 1, 1, 1], [0, 1, 0, 0, 1, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge8_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen8 (gen8 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen8 0 (![true, false])]

  right
  refine ⟨16, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original16_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen8 0 (![true, false]))) original16
    (![[], [0], [1, 4, 1], [0, 3, 2, 5]])
    (![[1], [1, 1], [1, 3, 1, 1], [1, 1, 1, 1], [1, 1, 2, 1, 1], [1, 2, 1, 2, 3, 3, 2], [1, 1, 2, 3, 3], [1, 2, 3, 2, 3, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge8_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen8 (gen8 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen8 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen8 1 (![false, true])) k ∈ character.ker) k

private theorem edge8_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen8 (gen8 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen8 0 (![true, true])]

  right
  refine ⟨16, rootOne ^ 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original16_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 3)).toMonoidHom ∘ (flatSchreier gen8 0 (![true, true]))) original16
    (![[], [2, 0, 5], [0, 4, 0, 1, 8], [4, 0]])
    (![[1, 3, 2, 1, 3, 3], [1, 1, 1, 1, 2, 1, 1], [1, 1, 3, 2, 1], [1, 3, 2, 1, 2, 3], [1, 3, 2, 1, 3], [3, 1, 1, 2, 3], [3, 2, 3, 1, 1], [1, 1, 2, 3, 2, 3, 2], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks8 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen8 (gen8 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge8_1⟩

  · exact Or.inr ⟨1, by decide, edge8_2⟩

  · exact Or.inr ⟨0, by decide, edge8_3⟩

private theorem step8 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 8)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 8 gen8 gen8_eq checks8 H hm hp

private def gen9 : Fin 2 → SylowModel := ![root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen9_eq : Subgroup.closure (Set.range gen9) = smallParityCensusNode 9 := by
  rw [← original9_eq]
  exact closure_eq_words gen9 original9
    (![[2], [0]])
    (![[1], [0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1], [0], [0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 1, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge9_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen9 (gen9 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen9 0 (![true, false])]

  right
  refine ⟨17, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original17_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen9 0 (![true, false]))) original17
    (![[], [0], [4, 3, 7], [0, 1, 2, 1]])
    (![[1], [1, 1], [3, 1, 3, 3], [1, 1, 1, 1], [1, 2, 3, 1, 3], [1, 2, 1, 3, 3], [3, 2, 1, 1, 3], [1, 2, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge9_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen9 (gen9 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen9 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen9 1 (![false, true])) k ∈ character.ker) k

private theorem edge9_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen9 (gen9 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen9 0 (![true, true])]

  right
  refine ⟨17, rootOne ^ 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original17_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 3)).toMonoidHom ∘ (flatSchreier gen9 0 (![true, true]))) original17
    (![[], [2, 0, 8], [1, 5, 1, 4], [0, 4, 8]])
    (![[1, 1, 3, 2, 1, 1], [1, 1, 1, 1, 2, 1, 1], [1, 3, 2, 3, 3], [1, 2, 3, 1, 3, 2], [1, 1, 1, 2, 1], [1, 1, 2, 3, 3], [3, 1, 2, 1, 3], [1, 1, 3, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks9 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen9 (gen9 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge9_1⟩

  · exact Or.inr ⟨1, by decide, edge9_2⟩

  · exact Or.inr ⟨0, by decide, edge9_3⟩

private theorem step9 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 9)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 9 gen9 gen9_eq checks9 H hm hp

private def gen10 : Fin 2 → SylowModel := ![root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 3 * root 3 * root 4]

private theorem gen10_eq : Subgroup.closure (Set.range gen10) = smallParityCensusNode 10 := by
  rw [← original10_eq]
  exact closure_eq_words gen10 original10
    (![[2], [0]])
    (![[1], [0, 1, 0, 1, 0, 1, 1, 1, 0, 1], [0], [0, 0, 1, 0, 1, 0, 0, 0, 1, 1], [0, 1, 1, 1, 0, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1, 1], [1, 1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge10_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen10 (gen10 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen10 0 (![true, false])]

  right
  refine ⟨18, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original18_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen10 0 (![true, false]))) original18
    (![[], [0], [2], [3, 0, 4, 5]])
    (![[1], [1, 1], [2], [2, 1, 2, 1, 1, 3], [1, 1, 2, 3, 3, 2], [1, 1, 1, 2, 1, 2], [3, 1, 3, 1], [1, 1, 1, 3, 3, 1, 3, 3], [1, 1, 1, 3, 2, 3, 3, 3, 1, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge10_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen10 (gen10 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen10 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen10 1 (![false, true])) k ∈ character.ker) k

private theorem edge10_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen10 (gen10 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen10 0 (![true, true])]

  right
  refine ⟨18, rootOne ^ 2 * root 0 * root 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original18_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 2 * root 0 * root 3)).toMonoidHom ∘ (flatSchreier gen10 0 (![true, true]))) original18
    (![[], [0, 8], [2, 6], [0, 2, 3, 6]])
    (![[2, 3, 3, 2, 1, 3, 3], [1, 1], [1, 1, 2, 1, 1], [1, 1, 1, 3, 2], [1, 2, 1, 2, 3, 3], [1, 2, 1, 2, 1, 1], [1, 1, 2, 1, 1, 2], [3, 3, 3, 3], [1, 1, 1, 2, 3, 3, 2, 1, 3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem checks10 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen10 (gen10 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge10_1⟩

  · exact Or.inr ⟨1, by decide, edge10_2⟩

  · exact Or.inr ⟨0, by decide, edge10_3⟩

private theorem step10 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 10)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 10 gen10 gen10_eq checks10 H hm hp

private def gen11 : Fin 4 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 3]

private theorem gen11_eq : Subgroup.closure (Set.range gen11) = smallParityCensusNode 11 := by
  rw [← original11_eq]
  exact closure_eq_words gen11 original11
    (![[1], [1, 3, 1, 2, 4], [4], [0]])
    (![[3], [0], [0, 0], [0, 1, 0, 0, 2, 0], [2], [0, 0, 2, 0, 2, 0], [0, 0, 0, 1, 3, 0, 3, 1], [1, 1, 3, 3], [3, 3], [2, 3, 2, 3, 3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, false, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, false, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen11 0 (![true, false, false, false])) k ∈ character.ker) k

private theorem edge11_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 1) (![false, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 1 (![false, true, false, false])]

  right
  refine ⟨20, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original20_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 1 (![false, true, false, false]))) original20
    (![[1], [], [2], [0], [0, 5, 1, 0], [2, 2], [2], [0, 2, 2]])
    (![[3], [0], [2], [0, 0], [0, 0, 0, 7, 0, 7], [0, 0, 0, 7, 4, 3], [3, 7], [0, 2, 0, 4, 2, 4], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, true, false, false])]

  right
  refine ⟨22, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original22_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, true, false, false]))) original22
    (![[], [2, 1, 3], [2], [0], [3], [2, 4, 5, 1], [4, 2], [0, 4]])
    (![[3], [2, 4, 1], [2], [4], [1, 5, 6, 2], [1, 4, 6, 1, 6], [5, 1], [1, 2, 5, 6], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 2) (![false, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 2 (![false, false, true, false])]

  right
  refine ⟨21, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original21_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 2 (![false, false, true, false]))) original21
    (![[1], [2, 2, 2, 5], [], [0], [1, 4], [2, 2, 2, 5], [6, 8], [0, 2, 2]])
    (![[3], [0], [0, 1, 0, 0, 4, 6], [0, 0], [0, 0, 0, 4], [0, 1, 4, 1, 0, 0], [3, 3, 6], [3, 3, 3, 6, 7], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, false, true, false])]

  right
  refine ⟨21, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original21_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, false, true, false]))) original21
    (![[], [2], [1, 3], [0, 7], [3, 4, 7], [1, 2, 1, 3], [1, 2, 2], [0, 4, 6, 7]])
    (![[2, 7, 6], [2, 2, 2], [1], [2, 2], [5, 3, 7, 5], [3, 1, 7, 5], [2, 1, 6, 5], [1, 7, 1, 7], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 1) (![false, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 1 (![false, true, true, false])]

  right
  refine ⟨19, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original19_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 1 (![false, true, true, false]))) original19
    (![[1], [], [1, 2, 1, 3], [0], [0, 5, 1, 0], [6, 8], [2, 5], [0, 6, 8]])
    (![[3], [0], [0, 0, 0, 2, 0], [0, 0], [0, 0, 0, 2, 4, 2], [0, 0, 0, 2, 0, 6], [3, 7], [0, 3, 0, 4, 7, 4], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, true, true, false])]

  right
  refine ⟨19, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original19_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, true, true, false]))) original19
    (![[], [1, 2, 3, 7], [1, 3], [0, 7], [3, 4, 7], [2, 1], [6, 1, 7], [0, 4, 6, 7]])
    (![[2, 7, 6], [2, 2, 2], [5, 2], [2, 2], [5, 3, 7, 1], [1, 6, 5, 2], [2, 1, 2, 1], [1, 3, 5, 7], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_8 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 3) (![false, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 3 (![false, false, false, true])]

  right
  refine ⟨15, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original15_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 3 (![false, false, false, true]))) original15
    (![[0], [0, 2, 0, 1, 3], [3], [], [0, 4, 6], [2, 5, 3], [3, 3, 3, 8], [7]])
    (![[0], [0, 0], [0, 0, 0, 2, 5, 0], [2], [0, 0, 0, 1, 1, 4], [0, 0, 0, 5, 4, 5], [1, 1, 7], [7], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_9 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, false, false, true])]

  right
  refine ⟨18, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original18_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, false, false, true]))) original18
    (![[], [0, 2, 0, 1, 3], [3, 8], [0, 1, 4, 7, 8], [1, 4, 7, 8], [4, 2, 3, 6], [4, 3], [0, 4, 8]])
    (![[3, 4], [3, 3], [5, 6], [1, 1, 5, 2, 5], [1, 2, 6, 1], [1, 2, 5, 6], [3, 1, 7, 5], [3, 7], [1, 6, 1, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_10 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 1) (![false, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 1 (![false, true, false, true])]

  right
  refine ⟨24, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original24_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 1 (![false, true, false, true]))) original24
    (![[1], [], [2], [0, 5, 2], [0, 1, 0, 6], [2, 2], [2], [0, 5, 2]])
    (![[0, 0, 2, 4, 3, 4], [0], [2], [0, 0], [0, 2, 0, 2, 4, 4], [0, 0, 3, 0, 3, 0], [3, 3, 5], [0, 2, 0, 4, 2, 4], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_11 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, true, false, true])]

  right
  refine ⟨26, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original26_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, true, false, true]))) original26
    (![[], [2, 1, 3], [2], [0, 1, 5, 3], [3], [2, 4, 5, 1], [4, 2], [1, 0]])
    (![[7, 6, 1], [2, 4, 1], [2], [4], [1, 5, 6, 2], [3, 5, 7, 1], [5, 1], [1, 2, 5, 6], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_12 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 2) (![false, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 2 (![false, false, true, true])]

  right
  refine ⟨25, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original25_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 2 (![false, false, true, true]))) original25
    (![[1], [2, 2, 2, 5], [], [0, 6, 8], [1, 4], [2, 2, 2, 5], [6, 8], [0, 2, 2]])
    (![[3, 6], [0], [0, 1, 0, 0, 4, 6], [0, 0], [0, 0, 0, 4], [0, 1, 4, 1, 0, 0], [3, 6, 7], [3, 3, 3, 7], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_13 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, false, true, true])]

  right
  refine ⟨25, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original25_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, false, true, true]))) original25
    (![[], [2], [1, 3], [0, 5, 1, 3], [3, 4, 7], [1, 2, 1, 3], [1, 2, 2], [0, 1, 5, 7]])
    (![[1, 4, 5, 2, 3], [2, 2, 2], [1], [2, 2], [1, 6, 5, 4, 6], [1, 2, 2, 4, 5], [2, 1, 6, 5], [2, 3, 2, 3], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_14 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 1) (![false, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 1 (![false, true, true, true])]

  right
  refine ⟨23, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original23_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen11 1 (![false, true, true, true]))) original23
    (![[1], [], [1, 2, 1, 3], [0, 2, 5], [0, 0, 4, 5, 1], [6, 8], [2, 5], [0, 2, 5]])
    (![[3, 6], [0], [0, 0, 0, 2, 0], [0, 0], [0, 0, 0, 2, 4, 2], [0, 0, 0, 2, 0, 6], [3, 3, 5], [2, 3, 2, 3, 3, 3], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge11_15 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 0) (![true, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen11 0 (![true, true, true, true])]

  right
  refine ⟨23, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original23_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen11 0 (![true, true, true, true]))) original23
    (![[], [1, 2, 3, 7], [1, 3], [0, 5, 1, 3], [3, 4, 7], [2, 1], [6, 1, 7], [0, 1, 5, 7]])
    (![[1, 1, 2, 3], [2, 2, 2], [5, 2], [2, 2], [1, 2, 1, 4, 6], [1, 6, 5, 2], [2, 1, 2, 1], [2, 3, 2, 3], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem checks11 (σ : Fin 4 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen11 (gen11 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true] := by
    exact (by decide : ∀ σ : Fin 4 → Bool, σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge11_1⟩

  · exact Or.inr ⟨1, by decide, edge11_2⟩

  · exact Or.inr ⟨0, by decide, edge11_3⟩

  · exact Or.inr ⟨2, by decide, edge11_4⟩

  · exact Or.inr ⟨0, by decide, edge11_5⟩

  · exact Or.inr ⟨1, by decide, edge11_6⟩

  · exact Or.inr ⟨0, by decide, edge11_7⟩

  · exact Or.inr ⟨3, by decide, edge11_8⟩

  · exact Or.inr ⟨0, by decide, edge11_9⟩

  · exact Or.inr ⟨1, by decide, edge11_10⟩

  · exact Or.inr ⟨0, by decide, edge11_11⟩

  · exact Or.inr ⟨2, by decide, edge11_12⟩

  · exact Or.inr ⟨0, by decide, edge11_13⟩

  · exact Or.inr ⟨1, by decide, edge11_14⟩

  · exact Or.inr ⟨0, by decide, edge11_15⟩

private theorem step11 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 11)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 11 gen11 gen11_eq checks11 H hm hp

private def gen12 : Fin 2 → SylowModel := ![rootOne ^ 3, root 1 * root 5 * root 6 * root 7 * root 8 * root 9]

private theorem gen12_eq : Subgroup.closure (Set.range gen12) = smallParityCensusNode 12 := by
  rw [← original12_eq]
  exact closure_eq_words gen12 original12
    (![[1], [0]])
    (![[1], [0], [0, 0], [0, 1, 0, 1, 0, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 1, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 1, 0, 0, 1, 1], [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge12_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen12 (gen12 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen12 0 (![true, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen12 0 (![true, false])) k ∈ character.ker) k

private theorem edge12_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen12 (gen12 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen12 1 (![false, true])]

  right
  refine ⟨15, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original15_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen12 1 (![false, true]))) original15
    (![[0], [], [3, 0, 5], [2, 7, 8]])
    (![[0], [0, 0], [0, 2, 3, 0, 2], [0, 2, 2, 3, 2, 3], [0, 0, 3, 2, 2, 3], [0, 0, 0, 3, 0, 3], [0, 0, 3, 0, 0, 3], [0, 0, 2, 0, 0, 2, 2, 2], [0, 0, 0, 2, 0, 0, 3, 0, 2, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge12_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen12 (gen12 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen12 0 (![true, true])]

  right
  refine ⟨18, rootOne ^ 2 * root 0 * root 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original18_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 2 * root 0 * root 3)).toMonoidHom ∘ (flatSchreier gen12 0 (![true, true]))) original18
    (![[], [0, 4, 5, 1], [0, 3, 2, 0], [4, 2, 0]])
    (![[1, 1, 2, 1, 2], [3, 1, 1, 1, 3, 1], [1, 1, 3, 3, 3, 1], [1, 2, 1, 1, 3], [1, 2, 1, 3, 3, 2], [1, 2, 3, 3, 2, 1], [1, 1, 2, 1, 1, 2], [3, 3, 3, 3], [1, 2, 3, 2, 1, 2, 3, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks12 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen12 (gen12 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge12_1⟩

  · exact Or.inr ⟨1, by decide, edge12_2⟩

  · exact Or.inr ⟨0, by decide, edge12_3⟩

private theorem step12 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 12)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 12 gen12 gen12_eq checks12 H hm hp

private def gen13 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen13_eq : Subgroup.closure (Set.range gen13) = smallParityCensusNode 13 := by
  rw [← original13_eq]
  exact closure_eq_words gen13 original13
    (![[3, 8], [0], [1]])
    (![[1], [2], [1, 1], [0, 0, 2, 1, 1, 0, 2], [1, 1, 1, 1], [1, 1, 0, 2, 2, 0], [2, 0, 2, 0, 1, 1], [0, 0, 0, 2, 0, 2, 1, 1], [0, 2, 1, 1, 0, 2], [0, 1, 0, 1, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 0 (![true, false, false])]

  right
  refine ⟨27, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original27_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen13 0 (![true, false, false]))) original27
    (![[], [0], [1], [6], [3, 6, 0], [3, 1, 7]])
    (![[1], [2], [1, 1], [1, 2, 5, 4], [1, 1, 1, 1], [2, 2, 1, 4], [3], [1, 1, 5, 3, 2], [1, 1, 3, 5, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 1 (![false, true, false])]

  right
  refine ⟨17, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original17_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen13 1 (![false, true, false]))) original17
    (![[2, 5], [], [0], [2, 4, 8], [0, 4, 0, 3], [0, 4, 3, 7]])
    (![[2], [2, 2], [2, 2, 2, 5, 3], [0, 0, 4, 4], [5, 5, 5, 2], [0, 2, 4, 2, 3], [3, 3], [0, 0, 3, 3], [4, 4, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 0 (![true, true, false])]

  right
  refine ⟨28, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original28_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen13 0 (![true, true, false]))) original28
    (![[], [0, 4, 8], [2, 1, 2], [6, 8], [3, 4, 6, 0], [3, 4, 1]])
    (![[1, 1, 1, 1, 1], [1, 1, 2, 1, 1], [3, 1, 1, 3], [4, 2, 5, 4], [1, 1, 1, 1], [4, 1, 5, 2], [5, 2, 1, 4], [1, 1, 5, 5], [2, 2, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 2 (![false, false, true])]

  right
  refine ⟨16, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original16_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen13 2 (![false, false, true]))) original16
    (![[2, 7], [0], [], [2, 4, 5, 6], [0, 4, 3, 6], [3, 4, 1, 5]])
    (![[1], [1, 1], [4, 5, 4, 3], [0, 0, 5, 5], [5, 4, 4], [0, 4, 0, 4, 5], [0, 3, 1, 1, 5], [0, 0, 3, 3], [5, 5, 5, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 0 (![true, false, true])]

  right
  refine ⟨28, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original28_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen13 0 (![true, false, true]))) original28
    (![[], [0], [6, 1, 8], [6], [3, 6, 0], [1, 3, 5]])
    (![[1], [1, 1, 4, 5, 1], [1, 1], [2, 2, 1, 4], [1, 1, 1, 1], [2, 1, 1, 2], [3], [1, 1, 5, 5], [2, 2, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge13_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 1 (![false, true, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen13 1 (![false, true, true])) k ∈ character.ker) k

private theorem edge13_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen13 0 (![true, true, true])]

  right
  refine ⟨27, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original27_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen13 0 (![true, true, true]))) original27
    (![[], [0, 4, 8], [1, 4, 5, 8], [6, 8], [3, 4, 6, 0], [1, 3, 4]])
    (![[1, 1, 1, 1, 1], [1, 1, 2, 1, 1], [3, 1, 1, 3], [2, 1, 4, 5], [1, 1, 1, 1], [1, 5, 5, 4], [1, 2, 2, 4, 3], [1, 1, 5, 2], [1, 2, 2, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks13 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen13 (gen13 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge13_1⟩

  · exact Or.inr ⟨1, by decide, edge13_2⟩

  · exact Or.inr ⟨0, by decide, edge13_3⟩

  · exact Or.inr ⟨2, by decide, edge13_4⟩

  · exact Or.inr ⟨0, by decide, edge13_5⟩

  · exact Or.inr ⟨1, by decide, edge13_6⟩

  · exact Or.inr ⟨0, by decide, edge13_7⟩

private theorem step13 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 13)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 13 gen13 gen13_eq checks13 H hm hp

private def gen14 : Fin 2 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 3]

private theorem gen14_eq : Subgroup.closure (Set.range gen14) = smallParityCensusNode 14 := by
  rw [← original14_eq]
  exact closure_eq_words gen14 original14
    (![[0], [1]])
    (![[0], [1], [0, 0], [1, 0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1], [0, 1, 0, 1], [0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]])
    (by decide +kernel) (by decide +kernel)

private theorem edge14_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen14 (gen14 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen14 0 (![true, false])]

  right
  refine ⟨17, rootOne ^ 3, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original17_eq]
  exact closure_eq_words ((MulAut.conj (rootOne ^ 3)).toMonoidHom ∘ (flatSchreier gen14 0 (![true, false]))) original17
    (![[], [3, 2, 4, 0], [2, 1, 3, 6], [3, 4, 7, 0]])
    (![[2, 1, 3, 2, 3, 2], [1, 2, 3, 1, 1], [1, 1, 2, 3, 1, 2], [1, 1, 1, 1, 2, 1, 3], [1, 1, 2, 2, 3, 3], [1, 1, 1, 1, 2, 2], [1, 3, 2], [1, 2, 1, 3, 3, 2], [2, 2, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge14_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen14 (gen14 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen14 1 (![false, true])]

  right
  refine ⟨16, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original16_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen14 1 (![false, true]))) original16
    (![[0], [], [0, 2, 6], [3, 2, 1, 6]])
    (![[0], [0, 0], [2, 0, 2, 2, 3, 3], [0, 0, 0, 0], [3, 2, 0], [3, 2, 3, 2, 0, 0], [0, 2, 3], [0, 2, 3, 2, 3, 0], [3, 3, 3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge14_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen14 (gen14 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen14 0 (![true, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen14 0 (![true, true])) k ∈ character.ker) k

private theorem checks14 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen14 (gen14 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge14_1⟩

  · exact Or.inr ⟨1, by decide, edge14_2⟩

  · exact Or.inr ⟨0, by decide, edge14_3⟩

private theorem step14 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 14)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 14 gen14 gen14_eq checks14 H hm hp

private def gen15 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7]

private theorem gen15_eq : Subgroup.closure (Set.range gen15) = smallParityCensusNode 15 := by
  rw [← original15_eq]
  exact closure_eq_words gen15 original15
    (![[0], [0, 2, 0, 1, 3], [3]])
    (![[0], [0, 0], [0, 1, 0, 0, 2, 0], [2], [0, 0, 2, 0, 2, 0], [0, 1, 0, 0, 2, 0, 1, 2], [0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 1, 1], [0, 1, 0, 2, 0, 1, 1, 1, 0, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 0 (![true, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen15 0 (![true, false, false])) k ∈ character.ker) k

private theorem edge15_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 1 (![false, true, false])]

  right
  refine ⟨30, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original30_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen15 1 (![false, true, false]))) original30
    (![[0], [], [1], [1, 0, 4, 1], [1, 1], [1]])
    (![[0], [2], [0, 0], [0, 2, 3, 3, 0, 2], [0, 2, 3, 0, 0, 2], [0, 3, 3, 0], [0, 2, 0, 3, 2, 3], [0, 3, 0, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 0 (![true, true, false])]

  right
  refine ⟨32, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original32_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen15 0 (![true, true, false]))) original32
    (![[], [1, 0, 2], [1], [2], [3, 1, 4, 0], [1, 3]])
    (![[2, 3, 1], [2], [3], [1, 4, 2, 5], [1, 3, 5, 1, 5], [4, 1], [1, 2, 4, 5], [1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 2 (![false, false, true])]

  right
  refine ⟨31, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original31_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen15 2 (![false, false, true]))) original31
    (![[0], [1, 1, 1, 4], [], [0, 3, 7], [1, 1, 1, 4], [5, 7]])
    (![[0], [0, 1, 0, 0, 3, 5], [0, 0], [0, 0, 0, 5, 3, 5], [0, 1, 3, 1, 0, 0], [0, 0, 0, 5, 0], [0, 1, 0, 1, 3, 1, 3, 1], [0, 0, 0, 5, 0, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 0 (![true, false, true])]

  right
  refine ⟨31, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original31_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen15 0 (![true, false, true]))) original31
    (![[], [1], [0, 2], [1, 2, 1, 3], [0, 1, 0, 2], [0, 1, 1]])
    (![[2, 2, 2], [1], [2, 2], [1, 2, 2, 1, 3], [1, 2, 2, 3, 4], [2, 1, 5, 4], [1, 1, 1, 5, 4, 2], [1, 1, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 1 (![false, true, true])]

  right
  refine ⟨29, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original29_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen15 1 (![false, true, true]))) original29
    (![[0], [], [0, 1, 0, 2], [3, 4, 0, 6], [5, 7], [1, 4]])
    (![[0], [0, 0, 0, 2, 0], [0, 0], [0, 0, 0, 5, 3, 5], [0, 0, 0, 2, 0, 5], [0, 3, 3, 0], [0, 2, 0, 3, 5, 3, 4], [0, 3, 0, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge15_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen15 0 (![true, true, true])]

  right
  refine ⟨29, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original29_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen15 0 (![true, true, true]))) original29
    (![[], [0, 1, 2, 6], [0, 2], [2, 3, 6, 7], [1, 0], [5, 0, 6]])
    (![[2, 2, 2], [4, 2], [2, 2], [1, 5, 5, 4, 3], [1, 5, 4, 2], [2, 1, 2, 1], [1, 2, 1, 2, 1, 4], [1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks15 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen15 (gen15 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge15_1⟩

  · exact Or.inr ⟨1, by decide, edge15_2⟩

  · exact Or.inr ⟨0, by decide, edge15_3⟩

  · exact Or.inr ⟨2, by decide, edge15_4⟩

  · exact Or.inr ⟨0, by decide, edge15_5⟩

  · exact Or.inr ⟨1, by decide, edge15_6⟩

  · exact Or.inr ⟨0, by decide, edge15_7⟩

private theorem step15 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 15)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 15 gen15 gen15_eq checks15 H hm hp

private def gen16 : Fin 2 → SylowModel := ![root 2 * root 3 * root 4 * root 7, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9]

private theorem gen16_eq : Subgroup.closure (Set.range gen16) = smallParityCensusNode 16 := by
  rw [← original16_eq]
  exact closure_eq_words gen16 original16
    (![[2, 7], [0]])
    (![[1], [1, 1], [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1, 0, 1], [1, 1, 1, 0, 1, 1, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge16_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen16 (gen16 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen16 0 (![true, false])]

  right
  refine ⟨33, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original33_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen16 0 (![true, false]))) original33
    (![[], [0], [5, 6], [0, 2, 6]])
    (![[1], [1, 1], [1, 1, 1, 3, 3, 3, 3, 3], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 3, 3], [1, 1, 1, 3, 1, 3, 1, 1], [1, 1, 1, 3, 3, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge16_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen16 (gen16 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen16 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen16 1 (![false, true])) k ∈ character.ker) k

private theorem edge16_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen16 (gen16 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen16 0 (![true, true])]

  right
  refine ⟨33, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original33_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen16 0 (![true, true]))) original33
    (![[], [0, 3, 7], [5, 6, 7], [0, 2, 3, 6]])
    (![[1, 1, 1, 1, 1], [2, 1, 1, 2], [1, 1, 1, 3, 3, 3, 3, 3], [1, 1, 1, 1], [1, 1, 1, 3, 1, 1, 3, 1], [1, 1, 1, 3, 1, 3, 1, 1], [1, 1, 1, 3, 3, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks16 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen16 (gen16 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge16_1⟩

  · exact Or.inr ⟨1, by decide, edge16_2⟩

  · exact Or.inr ⟨0, by decide, edge16_3⟩

private theorem step16 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 16)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 16 gen16 gen16_eq checks16 H hm hp

private def gen17 : Fin 2 → SylowModel := ![root 2 * root 3 * root 4 * root 7, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen17_eq : Subgroup.closure (Set.range gen17) = smallParityCensusNode 17 := by
  rw [← original17_eq]
  exact closure_eq_words gen17 original17
    (![[2, 5], [0]])
    (![[1], [1, 1], [1, 1, 1, 1, 1, 1, 0, 1, 1], [1, 1, 1, 1], [0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1], [1, 0, 1, 1, 0, 1, 1, 1, 1, 1], [1, 1, 0, 1, 1, 1, 1, 0, 1, 1], [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge17_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen17 (gen17 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen17 0 (![true, false])]

  right
  refine ⟨34, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original34_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen17 0 (![true, false]))) original34
    (![[], [0], [5, 6, 7], [5, 0, 2]])
    (![[1], [1, 1], [1, 1, 1, 1, 3, 1, 3, 3], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 1, 1], [1, 1, 1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 3, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge17_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen17 (gen17 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen17 1 (![false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen17 1 (![false, true])) k ∈ character.ker) k

private theorem edge17_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen17 (gen17 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen17 0 (![true, true])]

  right
  refine ⟨34, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original34_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen17 0 (![true, true]))) original34
    (![[], [0, 3, 4], [5, 6], [2, 3, 5, 0]])
    (![[1, 3, 3, 1, 1], [1, 2, 1], [1, 1, 1, 3, 3, 1, 3, 1], [1, 2, 3, 1, 3], [1, 1, 1, 3, 3, 3, 1, 3], [1, 1, 1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 3, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem checks17 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen17 (gen17 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge17_1⟩

  · exact Or.inr ⟨1, by decide, edge17_2⟩

  · exact Or.inr ⟨0, by decide, edge17_3⟩

private theorem step17 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 17)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 17 gen17 gen17_eq checks17 H hm hp

private def gen18 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, rootOne ^ 3 * root 3 * root 4]

private theorem gen18_eq : Subgroup.closure (Set.range gen18) = smallParityCensusNode 18 := by
  rw [← original18_eq]
  exact closure_eq_words gen18 original18
    (![[0, 2, 0, 1, 3], [3, 8], [0]])
    (![[2], [2, 2], [2, 0, 1, 2, 2, 2], [0, 2, 2, 0, 1, 2, 2], [1, 2, 2, 2, 1, 2], [0, 1, 2, 0, 1, 2, 2, 2], [0, 0, 0, 2, 2, 0, 2, 2], [0, 0, 1, 2, 2, 1, 2, 2], [0, 0, 0, 1, 2, 2, 0, 1, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 0 (![true, false, false])]

  right
  refine ⟨36, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original36_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen18 0 (![true, false, false]))) original36
    (![[], [1, 6], [0], [1, 1], [1, 6], [1, 0, 1, 4]])
    (![[2], [1, 2, 2, 5, 3, 5], [2, 2], [1, 2, 2, 5, 1, 5], [1, 2, 1, 2, 2, 5], [2, 2, 5, 5], [2, 2, 5, 3, 5], [2, 5, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 1 (![false, true, false])]

  right
  refine ⟨37, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original37_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen18 1 (![false, true, false]))) original37
    (![[1, 1, 4, 1], [], [0], [1, 1, 4, 1], [1, 1, 6], [3, 0]])
    (![[2], [2, 5, 5, 0, 5], [2, 2], [2, 2, 5, 2], [0, 2, 5, 5, 0, 5], [0, 2, 2, 0, 2, 2, 4], [0, 2, 2, 0, 5, 5], [2, 2, 5, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 0 (![true, true, false])]

  right
  refine ⟨35, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original35_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen18 0 (![true, true, false]))) original35
    (![[], [0, 1, 0, 2, 6], [0], [5, 6, 7], [1, 4], [4, 0, 3, 6]])
    (![[2], [2, 4, 2, 2, 2], [2, 2], [1, 2, 4, 5, 2, 2], [1, 2, 1, 5, 2, 5], [2, 2, 5, 5], [2, 2, 5, 3, 5], [2, 5, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 2 (![false, false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen18 2 (![false, false, true])) k ∈ character.ker) k

private theorem edge18_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 0 (![true, false, true])]

  right
  refine ⟨38, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original38_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen18 0 (![true, false, true]))) original38
    (![[], [1, 6], [0, 1, 4], [1, 1], [1, 6], [1, 0]])
    (![[1, 2, 2, 5, 5, 5], [1, 2, 2, 3, 5, 5], [2, 5], [1, 2, 5, 5, 1, 2], [1, 2, 5, 5, 1, 5], [2, 5, 5, 2], [2, 2, 3, 5, 5], [2, 2, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 1 (![false, true, true])]

  right
  refine ⟨37, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original37_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen18 1 (![false, true, true]))) original37
    (![[1, 6], [], [0, 6], [1, 6], [1, 1], [3, 0, 6]])
    (![[0, 2, 5, 0, 2, 2, 5], [2, 4, 5, 0, 2, 5], [2, 2], [2, 2, 5, 2], [0, 5, 0, 2, 2, 2], [2, 2, 2, 4, 2], [0, 2, 5, 0, 5, 2], [2, 2, 5, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge18_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen18 0 (![true, true, true])]

  right
  refine ⟨35, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original35_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen18 0 (![true, true, true]))) original35
    (![[], [0, 1, 0, 2], [1, 5, 0, 6], [5, 7], [1, 4], [3, 0, 1]])
    (![[2, 2, 2, 1, 5, 5], [2, 4, 5, 2, 5], [2, 1, 2, 1], [1, 2, 2, 2, 1, 5], [1, 2, 1, 2, 2, 2], [2, 2, 2, 2, 3], [2, 2, 3, 5, 5], [2, 2, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks18 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen18 (gen18 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge18_1⟩

  · exact Or.inr ⟨1, by decide, edge18_2⟩

  · exact Or.inr ⟨0, by decide, edge18_3⟩

  · exact Or.inr ⟨2, by decide, edge18_4⟩

  · exact Or.inr ⟨0, by decide, edge18_5⟩

  · exact Or.inr ⟨1, by decide, edge18_6⟩

  · exact Or.inr ⟨0, by decide, edge18_7⟩

private theorem step18 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 18)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 18 gen18 gen18_eq checks18 H hm hp

private def gen19 : Fin 3 → SylowModel := ![rootOne ^ 3, root 3, root 5 * root 8]

private theorem gen19_eq : Subgroup.closure (Set.range gen19) = smallParityCensusNode 19 := by
  rw [← original19_eq]
  exact closure_eq_words gen19 original19
    (![[1], [0], [2]])
    (![[1], [0], [2], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 2, 0, 2], [0, 0, 2, 0, 0, 2], [0, 1, 2, 0, 2, 0, 1, 2, 0, 2], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 0 (![true, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen19 0 (![true, false, false])) k ∈ character.ker) k

private theorem edge19_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 1 (![false, true, false])]

  right
  refine ⟨29, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original29_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 1 (![false, true, false]))) original29
    (![[0], [], [1], [0, 3, 7], [7], [1]])
    (![[0], [2], [0, 0], [0, 0, 0, 3, 4], [0, 0, 0, 2, 0, 2], [0, 0, 2, 0, 0, 2], [0, 2, 0, 2, 3, 2, 3, 2, 4], [4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 0 (![true, true, false])]

  right
  refine ⟨35, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original35_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 0 (![true, true, false]))) original35
    (![[], [0, 2, 3, 5], [1], [2, 3, 5], [3, 0, 5], [0, 1, 0, 2, 6]])
    (![[1, 3], [2], [1, 1], [1, 3, 5, 1, 2], [2, 3, 5, 3], [1, 2, 4, 5], [1, 1, 1, 3, 5, 1, 3, 2], [1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 2 (![false, false, true])]

  right
  refine ⟨39, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original39_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 2 (![false, false, true]))) original39
    (![[1], [0], [], [1, 4], [0], []])
    (![[1], [0], [0, 0], [0, 1, 3, 0, 3, 1], [0, 0, 0, 3], [0, 0, 3, 3], [0, 1, 3, 0, 1, 3], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 0 (![true, false, true])]

  right
  refine ⟨40, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original40_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 0 (![true, false, true]))) original40
    (![[], [0], [1, 4, 2], [2], [0, 3], [1]])
    (![[1], [5], [3], [1, 1, 1, 4], [2, 2, 3], [2, 3, 5, 3], [1, 1, 1, 5, 4, 2], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 1 (![false, true, true])]

  right
  refine ⟨41, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original41_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 1 (![false, true, true]))) original41
    (![[1], [], [0, 7], [1, 3], [7], [0]])
    (![[5], [0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 2, 3, 5], [0, 0, 2, 0, 0, 5], [0, 2, 0, 2, 3, 2, 3, 5], [4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge19_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen19 0 (![true, true, true])]

  right
  refine ⟨42, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original42_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen19 0 (![true, true, true]))) original42
    (![[], [0, 1, 4, 2], [1, 4, 2], [2], [1, 0], [1]])
    (![[1, 5], [5], [3], [1, 1, 1, 3, 4], [2, 2, 3], [2, 3, 5, 3], [1, 1, 1, 3, 5, 3, 4, 5], [1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks19 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen19 (gen19 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge19_1⟩

  · exact Or.inr ⟨1, by decide, edge19_2⟩

  · exact Or.inr ⟨0, by decide, edge19_3⟩

  · exact Or.inr ⟨2, by decide, edge19_4⟩

  · exact Or.inr ⟨0, by decide, edge19_5⟩

  · exact Or.inr ⟨1, by decide, edge19_6⟩

  · exact Or.inr ⟨0, by decide, edge19_7⟩

private theorem step19 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 19)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 19 gen19 gen19_eq checks19 H hm hp

private def gen20 : Fin 4 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, root 6, root 3]

private theorem gen20_eq : Subgroup.closure (Set.range gen20) = smallParityCensusNode 20 := by
  rw [← original20_eq]
  exact closure_eq_words gen20 original20
    (![[1], [2], [5, 6, 7], [0]])
    (![[3], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [1, 1, 3, 2, 3], [1, 1, 3, 3], [1, 1, 1, 2, 1, 2], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, false, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, false, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen20 0 (![true, false, false, false])) k ∈ character.ker) k

private theorem edge20_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 1) (![false, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 1 (![false, true, false, false])]

  right
  refine ⟨39, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original39_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 1 (![false, true, false, false]))) original39
    (![[1], [], [4, 5, 6], [0], [1, 3], [5, 7], [4, 5], [0, 5, 6, 7]])
    (![[3], [0], [0, 0], [0, 0, 0, 4], [2, 3, 7], [3, 3, 5], [2, 6], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, true, false, false])]

  right
  refine ⟨39, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original39_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, true, false, false]))) original39
    (![[], [1, 2], [4, 5], [0, 6], [2, 3, 6], [5, 1, 6], [4, 6], [0, 3, 5, 6]])
    (![[1, 7, 5], [1, 1, 1], [1, 1], [1, 2, 1, 6, 4], [1, 1, 1, 2, 1], [1, 2, 5, 6], [1, 2, 5, 2], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 2) (![false, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 2 (![false, false, true, false])]

  right
  refine ⟨43, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original43_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 2 (![false, false, true, false]))) original43
    (![[1], [2], [], [0], [1, 2, 2], [2, 6], [], [0, 6]])
    (![[3], [0], [1], [0, 0], [0, 0, 0, 1, 4, 1], [1, 5], [1, 1, 1, 5], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, false, true, false])]

  right
  refine ⟨43, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original43_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, false, true, false]))) original43
    (![[], [2], [0, 1, 0, 3, 6], [0, 2, 2], [2, 2, 3], [2, 4, 6], [0, 1, 0, 6], [0, 4, 5, 7]])
    (![[1, 1, 3], [1, 5, 2, 4], [1], [2, 2], [1, 3, 1, 7], [1, 2, 5, 6], [1, 3, 5, 7], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 1) (![false, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 1 (![false, true, true, false])]

  right
  refine ⟨43, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original43_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 2 * root 4 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 1 (![false, true, true, false]))) original43
    (![[2, 1, 6], [], [0, 2, 0, 6], [0, 5], [2, 2, 1, 2], [5], [2, 7], [0, 6]])
    (![[3, 5], [4, 6], [2, 3, 7], [0, 2, 0, 2], [0, 0, 0, 4, 5], [5], [2, 2, 5], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, true, true, false])]

  right
  refine ⟨43, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original43_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, true, true, false]))) original43
    (![[], [1, 3], [2, 1, 2, 2, 3], [0, 6], [3, 4, 6], [1, 5], [1, 2, 7], [0, 4, 5, 7]])
    (![[1, 7, 5], [1, 1, 1], [1, 3, 3, 6], [1, 1], [1, 2, 5, 2, 4], [1, 5], [1, 3, 5, 7], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_8 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 3) (![false, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 3 (![false, false, false, true])]

  right
  refine ⟨30, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original30_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 3 (![false, false, false, true]))) original30
    (![[0], [1], [4, 5, 6], [], [0, 3, 7], [1, 1, 1, 6], [4, 5], [7]])
    (![[0], [1], [0, 0], [0, 0, 0, 4, 7], [1, 1, 6, 7], [1, 1, 7], [1, 5], [7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_9 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, false, false, true])]

  right
  refine ⟨36, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original36_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, false, false, true]))) original36
    (![[], [1, 6], [4, 5], [0, 2, 3, 5], [2, 3, 5], [1, 1, 3, 1], [4, 6], [3, 0, 5]])
    (![[3, 4], [2, 1, 2], [3, 3], [2, 5, 2, 1], [3, 2, 7], [2, 3, 2, 7], [1, 7, 5, 3], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_10 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 1) (![false, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 1 (![false, true, false, true])]

  right
  refine ⟨45, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original45_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 1 (![false, true, false, true]))) original45
    (![[1], [], [2, 5, 7], [0, 5, 6], [1, 4], [5, 6], [0, 0, 2, 5], [0, 5]])
    (![[3, 5], [0], [2, 3, 3, 5], [0, 0], [0, 0, 0, 4], [2, 5, 6], [2, 6], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_11 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, true, false, true])]

  right
  refine ⟨45, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original45_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, true, false, true]))) original45
    (![[], [1, 3], [0, 0, 2, 5], [0, 2, 1, 3], [3, 4, 6], [1, 5], [2, 6], [0, 1, 2, 6]])
    (![[1, 7, 6], [1, 1, 1], [3, 2, 7], [1, 1], [1, 2, 1, 6, 4], [1, 5], [1, 2, 5, 2], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_12 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 2) (![false, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 2 (![false, false, true, true])]

  right
  refine ⟨44, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original44_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen20 2 (![false, false, true, true]))) original44
    (![[1], [2], [], [0, 5, 7], [1, 2, 2], [2, 6], [], [0, 0, 0, 5]])
    (![[0, 0, 4, 0, 7], [0], [1], [0, 0], [0, 0, 0, 1, 4, 1], [1, 5], [1, 1, 1, 5], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_13 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, false, true, true])]

  right
  refine ⟨44, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original44_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, false, true, true]))) original44
    (![[], [2], [0, 0, 1, 3, 4], [1, 3, 0, 5], [2, 2, 3], [2, 4, 6], [0, 0, 1, 4], [1, 0, 4]])
    (![[2, 1, 7, 5], [1, 5, 2, 4], [1], [2, 2], [1, 7, 1, 3], [1, 2, 5, 6], [1, 7, 5, 3], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_14 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 1) (![false, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 1 (![false, true, true, true])]

  right
  refine ⟨44, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original44_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 2 * root 4 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 1 (![false, true, true, true]))) original44
    (![[2, 1, 6], [], [0, 0, 2, 5], [2, 0], [2, 2, 1, 2], [5], [2, 7], [0, 2, 5]])
    (![[2, 3, 3, 7], [4, 6], [3, 2, 7], [0, 2, 0, 2], [0, 0, 0, 4, 5], [5], [2, 2, 5], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge20_15 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 0) (![true, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen20 0 (![true, true, true, true])]

  right
  refine ⟨44, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original44_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen20 0 (![true, true, true, true]))) original44
    (![[], [1, 3], [2, 1, 2, 2, 3], [0, 2, 1, 3, 6], [3, 4, 6], [1, 5], [1, 2, 7], [1, 0, 2]])
    (![[3, 4, 2], [1, 1, 1], [1, 3, 7, 6], [1, 1], [2, 3, 6, 7], [1, 5], [1, 3, 1, 3], [3, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem checks20 (σ : Fin 4 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen20 (gen20 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true] := by
    exact (by decide : ∀ σ : Fin 4 → Bool, σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge20_1⟩

  · exact Or.inr ⟨1, by decide, edge20_2⟩

  · exact Or.inr ⟨0, by decide, edge20_3⟩

  · exact Or.inr ⟨2, by decide, edge20_4⟩

  · exact Or.inr ⟨0, by decide, edge20_5⟩

  · exact Or.inr ⟨1, by decide, edge20_6⟩

  · exact Or.inr ⟨0, by decide, edge20_7⟩

  · exact Or.inr ⟨3, by decide, edge20_8⟩

  · exact Or.inr ⟨0, by decide, edge20_9⟩

  · exact Or.inr ⟨1, by decide, edge20_10⟩

  · exact Or.inr ⟨0, by decide, edge20_11⟩

  · exact Or.inr ⟨2, by decide, edge20_12⟩

  · exact Or.inr ⟨0, by decide, edge20_13⟩

  · exact Or.inr ⟨1, by decide, edge20_14⟩

  · exact Or.inr ⟨0, by decide, edge20_15⟩

private theorem step20 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 20)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 20 gen20 gen20_eq checks20 H hm hp

private def gen21 : Fin 3 → SylowModel := ![rootOne ^ 3, root 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9]

private theorem gen21_eq : Subgroup.closure (Set.range gen21) = smallParityCensusNode 21 := by
  rw [← original21_eq]
  exact closure_eq_words gen21 original21
    (![[1], [0], [2]])
    (![[1], [0], [2], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 2, 1, 0, 2, 1], [0, 0, 2, 0, 0, 2, 2, 2], [0, 0, 1, 1, 2, 0, 0, 2], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 0 (![true, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen21 0 (![true, false, false])) k ∈ character.ker) k

private theorem edge21_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 1 (![false, true, false])]

  right
  refine ⟨31, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original31_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen21 1 (![false, true, false]))) original31
    (![[0], [], [1], [0, 3, 7], [7], [1, 1, 1]])
    (![[0], [2], [0, 0], [0, 0, 0, 3, 4], [0, 0, 0, 5, 3, 2], [0, 0, 2, 0, 0, 5], [0, 0, 2, 0, 0, 2, 4], [4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 0 (![true, true, false])]

  right
  refine ⟨37, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original37_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen21 0 (![true, true, false]))) original37
    (![[], [0, 2, 3, 5], [1, 6], [2, 3, 5], [3, 0, 5], [3, 1, 4]])
    (![[1, 3], [1, 3, 5, 3, 4], [1, 1], [1, 1, 3, 5, 5], [1, 1, 3, 2, 5], [5, 5], [1, 2, 3, 2, 3, 4], [1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 2 (![false, false, true])]

  right
  refine ⟨39, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original39_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen21 2 (![false, false, true]))) original39
    (![[1], [0], [], [1, 3, 4, 6], [0, 5, 6, 7], [5, 6, 7]])
    (![[1], [0], [0, 0], [0, 0, 0, 4, 0, 4], [0, 0, 0, 4, 3, 4], [0, 0, 3, 3], [0, 0, 3, 5, 3], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 0 (![true, false, true])]

  right
  refine ⟨40, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original40_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen21 0 (![true, false, true]))) original40
    (![[], [0, 6], [1, 4, 2], [2, 3, 6], [0, 3, 5, 6], [5, 1]])
    (![[1, 1, 5, 4, 2], [5, 2, 5], [1, 5, 1, 3, 2], [1, 2, 5, 4], [1, 3, 2, 1, 2], [5, 2], [1, 5, 4, 2], [1, 1]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 1 (![false, true, true])]

  right
  refine ⟨46, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original46_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen21 1 (![false, true, true]))) original46
    (![[1], [], [0, 5, 6], [1, 3], [7], [0]])
    (![[5], [0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 2, 0, 2], [0, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 4, 5], [4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge21_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen21 0 (![true, true, true])]

  right
  refine ⟨47, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original47_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen21 0 (![true, true, true]))) original47
    (![[], [1, 0, 2, 3], [2, 4, 1, 3], [2], [1, 0], [1]])
    (![[1, 5], [5], [3], [1, 1, 1, 3, 4], [1, 1, 3, 2, 3, 2], [2, 2, 2, 3, 2, 3], [1, 2, 1, 3, 2, 3], [1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks21 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen21 (gen21 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge21_1⟩

  · exact Or.inr ⟨1, by decide, edge21_2⟩

  · exact Or.inr ⟨0, by decide, edge21_3⟩

  · exact Or.inr ⟨2, by decide, edge21_4⟩

  · exact Or.inr ⟨0, by decide, edge21_5⟩

  · exact Or.inr ⟨1, by decide, edge21_6⟩

  · exact Or.inr ⟨0, by decide, edge21_7⟩

private theorem step21 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 21)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 21 gen21 gen21_eq checks21 H hm hp

private def gen22 : Fin 4 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 6, root 3, rootOne ^ 3 * root 5 * root 8]

private theorem gen22_eq : Subgroup.closure (Set.range gen22) = smallParityCensusNode 22 := by
  rw [← original22_eq]
  exact closure_eq_words gen22 original22
    (![[2], [5, 6, 7], [0], [1]])
    (![[2], [3], [0], [0, 1, 0, 3, 3], [2, 3, 2, 3, 3, 3], [0, 0, 2, 1, 2], [0, 0, 2, 2], [0, 0, 0, 1, 0, 1], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, false, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, false, false, false])]

  right
  refine ⟨40, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original40_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, false, false, false]))) original40
    (![[], [4, 5, 6], [0], [1], [5, 7], [4, 5], [0, 5, 6, 7], [1, 3]])
    (![[2], [3], [1, 4, 7, 7], [1, 3, 3, 1, 3, 7], [1, 2, 6], [2, 2, 4], [1, 5], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 1) (![false, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 1 (![false, true, false, false])]

  right
  refine ⟨48, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original48_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 1 (![false, true, false, false]))) original48
    (![[2], [], [0], [1], [2, 6], [], [0, 6], [1, 2, 2]])
    (![[2], [3], [0], [3, 3], [0, 3, 0, 3, 3, 7], [0, 4], [0, 0, 0, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, true, false, false])]

  right
  refine ⟨48, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original48_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 2 * root 4 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, true, false, false]))) original48
    (![[], [0, 2, 0, 6], [0, 5], [2, 1], [5], [2, 7], [0, 6], [5, 1, 2]])
    (![[2, 4], [7, 1, 4], [1, 2, 6], [1, 3, 1, 3], [3, 3, 7, 4, 3], [4], [1, 1, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 2) (![false, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 2 (![false, false, true, false])]

  right
  refine ⟨32, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original32_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 2 (![false, false, true, false]))) original32
    (![[1], [4, 5, 6], [], [0], [1, 1, 1, 6], [4, 5], [7], [3, 0, 7]])
    (![[3], [0], [3, 5, 3, 6], [3, 3, 7, 3], [0, 0, 5, 6], [0, 0, 6], [0, 4], [6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, false, true, false])]

  right
  refine ⟨50, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original50_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, false, true, false]))) original50
    (![[], [2, 5, 7], [0, 5, 6], [1], [5, 6], [0, 0, 2, 5], [0, 5], [4, 1]])
    (![[2, 4], [3], [1, 2, 2, 4], [3, 3], [1, 3, 3, 1, 7, 3], [1, 4, 5], [1, 5], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 1) (![false, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 1 (![false, true, true, false])]

  right
  refine ⟨49, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original49_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 1 (![false, true, true, false]))) original49
    (![[2], [], [0, 5, 7], [1], [2, 6], [], [0, 0, 0, 5], [1, 2, 2]])
    (![[0, 0, 2, 2, 2], [3], [0], [3, 3], [0, 3, 0, 3, 3, 7], [0, 4], [0, 0, 0, 4], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, true, true, false])]

  right
  refine ⟨49, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original49_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 2 * root 4 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, true, true, false]))) original49
    (![[], [0, 0, 2, 5], [2, 0], [2, 1], [5], [2, 7], [0, 2, 5], [5, 1, 2]])
    (![[1, 2, 2, 6], [7, 1, 4], [2, 1, 6], [1, 3, 1, 3], [3, 3, 7, 4, 3], [4], [1, 1, 4], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_8 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 3) (![false, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 3 (![false, false, false, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen22 3 (![false, false, false, true])) k ∈ character.ker) k

private theorem edge22_9 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, false, false, true])]

  right
  refine ⟨40, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original40_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, false, false, true]))) original40
    (![[], [4, 5], [0, 6], [1, 6], [5, 6, 7], [4, 5, 6], [0, 5, 6, 7], [1, 3]])
    (![[4, 6], [1, 5, 3], [1, 4, 7, 7], [1, 3, 3, 1, 7, 3], [1, 2, 6], [2, 6], [1, 5], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_10 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 1) (![false, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 1 (![false, true, false, true])]

  right
  refine ⟨48, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original48_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 1 (![false, true, false, true]))) original48
    (![[2], [], [0, 2, 2], [0, 1, 0], [2, 6], [], [0, 5], [4, 5, 1]])
    (![[0, 0, 2], [0, 7, 4], [0], [0, 3, 7, 0], [0, 3, 0, 3, 7, 3], [0, 4], [0, 0, 0, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_11 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, true, false, true])]

  right
  refine ⟨48, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original48_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, true, false, true]))) original48
    (![[], [0, 2, 0, 6], [0, 6], [1, 6], [5], [2, 7], [0, 5], [4, 1]])
    (![[4, 6], [1, 7, 5], [1, 2, 6], [3, 3], [1, 3, 3, 3, 7, 5], [4], [1, 1, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_12 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 2) (![false, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 2 (![false, false, true, true])]

  right
  refine ⟨38, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original38_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen22 2 (![false, false, true, true]))) original38
    (![[1, 6], [4, 5], [], [1, 0, 1], [1, 1, 1], [4, 5, 6], [7], [0]])
    (![[7], [0, 0, 4], [3, 5, 3, 6], [0, 0, 3, 3, 3, 7], [0, 0, 5, 6], [0, 0, 0, 4, 6], [0, 4], [6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_13 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, false, true, true])]

  right
  refine ⟨50, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original50_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, false, true, true]))) original50
    (![[], [0, 0, 2, 5], [0, 2], [1, 6], [5], [2, 5, 7], [0, 2, 6], [4, 1]])
    (![[1, 2, 2, 2, 4], [1, 5, 3], [1, 2, 2, 4], [3, 3], [1, 3, 3, 1, 3, 7], [4], [1, 5], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_14 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 1) (![false, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 1 (![false, true, true, true])]

  right
  refine ⟨49, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original49_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 1 (![false, true, true, true]))) original49
    (![[2], [], [0, 7], [1, 4, 7], [2, 6], [], [0, 0, 0], [4, 5, 1]])
    (![[2, 2, 6], [0, 7, 4], [0], [0, 3, 7, 0], [0, 3, 0, 3, 7, 3], [0, 4], [0, 0, 0, 4], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge22_15 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 0) (![true, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen22 0 (![true, true, true, true])]

  right
  refine ⟨49, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original49_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen22 0 (![true, true, true, true]))) original49
    (![[], [0, 0, 2, 5], [0, 2, 6], [1, 6], [5], [2, 7], [0, 2], [4, 1]])
    (![[2, 1, 2, 2], [1, 7, 5], [2, 1, 6], [3, 3], [1, 3, 3, 3, 7, 5], [4], [1, 1, 4], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem checks22 (σ : Fin 4 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen22 (gen22 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true] := by
    exact (by decide : ∀ σ : Fin 4 → Bool, σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge22_1⟩

  · exact Or.inr ⟨1, by decide, edge22_2⟩

  · exact Or.inr ⟨0, by decide, edge22_3⟩

  · exact Or.inr ⟨2, by decide, edge22_4⟩

  · exact Or.inr ⟨0, by decide, edge22_5⟩

  · exact Or.inr ⟨1, by decide, edge22_6⟩

  · exact Or.inr ⟨0, by decide, edge22_7⟩

  · exact Or.inr ⟨3, by decide, edge22_8⟩

  · exact Or.inr ⟨0, by decide, edge22_9⟩

  · exact Or.inr ⟨1, by decide, edge22_10⟩

  · exact Or.inr ⟨0, by decide, edge22_11⟩

  · exact Or.inr ⟨2, by decide, edge22_12⟩

  · exact Or.inr ⟨0, by decide, edge22_13⟩

  · exact Or.inr ⟨1, by decide, edge22_14⟩

  · exact Or.inr ⟨0, by decide, edge22_15⟩

private theorem step22 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 22)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 22 gen22 gen22_eq checks22 H hm hp

private def gen23 : Fin 4 → SylowModel := ![rootOne ^ 3, root 4 * root 7 * root 8, root 2 * root 4 * root 8, root 5 * root 8]

private theorem gen23_eq : Subgroup.closure (Set.range gen23) = smallParityCensusNode 23 := by
  rw [← original23_eq]
  exact closure_eq_words gen23 original23
    (![[1], [4, 6, 7], [0], [2]])
    (![[2], [0], [3], [0, 0], [0, 0, 3, 0, 0, 1, 3], [0, 0, 0, 3, 0, 3], [0, 0, 3, 0, 0, 3], [1, 2, 1, 2], [2, 3, 2, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, false, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, false, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen23 0 (![true, false, false, false])) k ∈ character.ker) k

private theorem edge23_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 1) (![false, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 1 (![false, true, false, false])]

  right
  refine ⟨51, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original51_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 1 (![false, true, false, false]))) original51
    (![[1], [], [0], [2], [1, 7], [], [0, 7], [2, 5, 7]])
    (![[2], [0], [3], [0, 0], [0, 0, 0, 3, 0, 3], [2, 2], [0, 0, 3, 0, 0, 3], [0, 0, 0, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, true, false, false])]

  right
  refine ⟨51, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original51_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, true, false, false]))) original51
    (![[], [3, 5, 6, 1], [0, 5, 6], [2, 5, 7], [3], [1, 5, 6], [0, 5, 6], [1, 2, 1, 3]])
    (![[1, 3, 5, 7, 2], [3, 5, 7], [1, 7, 5], [4], [1, 3, 5, 3], [2, 2], [3, 4, 3, 4], [1, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 2) (![false, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 2 (![false, false, true, false])]

  right
  refine ⟨29, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original29_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 2 (![false, false, true, false]))) original29
    (![[0], [3, 5, 6, 7], [], [1], [0], [3, 5, 6], [6, 7], [1, 6]])
    (![[0], [3], [0, 0], [0, 0, 3, 0, 0, 5, 3], [0, 0, 0, 3, 0, 3], [0, 0, 3, 0, 0, 3], [3, 7], [1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, false, true, false])]

  right
  refine ⟨35, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original35_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, false, true, false]))) original35
    (![[], [3, 5, 7], [0, 1, 2, 3, 1], [1], [2, 6, 7], [3, 5], [3, 0, 5], [0, 1, 0, 2]])
    (![[1, 6], [3], [2, 2], [1, 3, 6, 7, 2], [3, 4, 7, 4], [2, 3, 6, 7], [1, 2, 5, 6], [1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 1) (![false, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 1 (![false, true, true, false])]

  right
  refine ⟨53, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original53_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 1 (![false, true, true, false]))) original53
    (![[1], [], [0, 0, 0, 6], [2], [1, 7], [], [0, 5, 6], [0, 0, 2]])
    (![[0, 0, 2, 3, 0, 0, 7], [0], [3], [0, 0], [0, 0, 0, 3, 0, 3], [2, 6], [0, 0, 3, 0, 0, 3], [0, 0, 0, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, true, true, false])]

  right
  refine ⟨53, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original53_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, true, true, false]))) original53
    (![[], [3, 5, 6, 1], [0, 3, 5, 6, 1], [0, 0, 2], [3], [1, 5, 6], [0, 5, 6, 1], [1, 2, 1, 3]])
    (![[2, 5], [3, 5, 7], [1, 7, 5], [4], [1, 3, 5, 3], [2, 6], [2, 3, 6, 7], [1, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_8 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 3) (![false, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 3 (![false, false, false, true])]

  right
  refine ⟨45, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original45_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 3 (![false, false, false, true]))) original45
    (![[1], [4, 5, 7], [0], [], [1, 2], [0, 0, 4, 5], [0, 6], []])
    (![[2], [0], [0, 0, 0, 4], [0, 0], [0, 0, 4, 4, 5], [0, 0, 1, 4, 5, 4], [1, 5], [2, 6]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_9 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, false, false, true])]

  right
  refine ⟨50, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original50_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, false, false, true]))) original50
    (![[], [0, 0, 4, 5], [0], [1, 3, 7], [3, 2], [4, 5, 6], [0], [1]])
    (![[2], [7], [3, 3, 4], [7, 7], [1, 3, 4, 7, 4], [1, 3, 1, 4, 7, 4], [1, 2, 1, 2], [1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_10 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 1) (![false, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 1 (![false, true, false, true])]

  right
  refine ⟨52, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original52_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 1 (![false, true, false, true]))) original52
    (![[1], [], [0], [2, 2, 2, 6], [1, 7], [], [0, 7], [2, 6]])
    (![[2], [0], [0, 0, 7, 0, 0], [0, 0], [0, 0, 0, 3, 4, 7], [2, 2], [0, 0, 3, 0, 0, 7], [0, 0, 0, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_11 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, true, false, true])]

  right
  refine ⟨52, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original52_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, true, false, true]))) original52
    (![[], [1, 2, 3, 2], [0, 5, 6], [1, 2, 3, 4, 5], [3], [1, 5, 6], [0, 5, 6], [1, 2]])
    (![[1, 3, 1, 3, 2], [3, 1, 3], [4, 3, 1], [4], [5, 7, 1, 3], [2, 2], [3, 4, 7, 4], [1, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_12 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 2) (![false, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 2 (![false, false, true, true])]

  right
  refine ⟨46, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original46_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 2 (![false, false, true, true]))) original46
    (![[1], [3, 5, 6], [], [0, 6, 7], [1], [3, 5, 6, 7], [6, 7], [0, 6]])
    (![[3, 6], [0], [0, 0], [0, 0, 3, 0, 0, 1, 3], [0, 0, 0, 3, 0, 7], [0, 0, 3, 0, 0, 7], [1, 5, 6], [1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_13 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, false, true, true])]

  right
  refine ⟨47, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original47_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, false, true, true]))) original47
    (![[], [3], [1, 0, 2, 3, 6], [1, 1, 1, 4], [2, 3, 6], [3, 7], [1, 0], [4, 1, 7]])
    (![[7, 2], [4, 3], [2, 2, 5], [1], [3, 3, 4], [2, 2, 7, 4, 3], [1, 2, 5, 6], [1, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_14 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 1) (![false, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 1 (![false, true, true, true])]

  right
  refine ⟨54, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original54_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen23 1 (![false, true, true, true]))) original54
    (![[1], [], [0, 0, 0, 6], [0, 0, 2, 6], [1, 7], [], [0, 5, 6], [2, 6]])
    (![[0, 0, 2, 3, 0, 0, 3], [0], [0, 0, 7, 0, 0], [0, 0], [0, 0, 0, 3, 4, 7], [2, 6], [0, 0, 3, 0, 0, 7], [0, 0, 0, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge23_15 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 0) (![true, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen23 0 (![true, true, true, true])]

  right
  refine ⟨54, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original54_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen23 0 (![true, true, true, true]))) original54
    (![[], [1, 2, 3, 2], [0, 1, 2, 3, 2], [0, 0, 2, 1, 3], [3], [1, 5, 6], [0, 5, 6, 1], [1, 2]])
    (![[2, 5], [3, 1, 3], [4, 3, 1], [4], [2, 2, 3, 3], [2, 6], [2, 3, 2, 3], [1, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks23 (σ : Fin 4 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen23 (gen23 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true] := by
    exact (by decide : ∀ σ : Fin 4 → Bool, σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge23_1⟩

  · exact Or.inr ⟨1, by decide, edge23_2⟩

  · exact Or.inr ⟨0, by decide, edge23_3⟩

  · exact Or.inr ⟨2, by decide, edge23_4⟩

  · exact Or.inr ⟨0, by decide, edge23_5⟩

  · exact Or.inr ⟨1, by decide, edge23_6⟩

  · exact Or.inr ⟨0, by decide, edge23_7⟩

  · exact Or.inr ⟨3, by decide, edge23_8⟩

  · exact Or.inr ⟨0, by decide, edge23_9⟩

  · exact Or.inr ⟨1, by decide, edge23_10⟩

  · exact Or.inr ⟨0, by decide, edge23_11⟩

  · exact Or.inr ⟨2, by decide, edge23_12⟩

  · exact Or.inr ⟨0, by decide, edge23_13⟩

  · exact Or.inr ⟨1, by decide, edge23_14⟩

  · exact Or.inr ⟨0, by decide, edge23_15⟩

private theorem step23 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 23)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 23 gen23 gen23_eq checks23 H hm hp

private def gen24 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, root 3 * root 5 * root 8]

private theorem gen24_eq : Subgroup.closure (Set.range gen24) = smallParityCensusNode 24 := by
  rw [← original24_eq]
  exact closure_eq_words gen24 original24
    (![[1], [2], [0]])
    (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 1, 2, 0, 1, 2], [1, 1, 2, 2], [0, 1, 0, 1, 2, 0, 1, 0, 2, 1], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 0 (![true, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen24 0 (![true, false, false])) k ∈ character.ker) k

private theorem edge24_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 1 (![false, true, false])]

  right
  refine ⟨41, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original41_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen24 1 (![false, true, false]))) original41
    (![[1], [], [0], [1, 3], [5, 7], [0, 5, 7]])
    (![[2], [0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 5, 3, 5], [2, 5], [0, 2, 0, 3, 5, 3], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 0 (![true, true, false])]

  right
  refine ⟨41, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original41_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen24 0 (![true, true, false]))) original41
    (![[], [1, 2], [0, 6], [2, 3, 6], [5, 1, 6], [3, 0, 4, 7]])
    (![[1, 2, 5, 4, 5], [1, 1, 1], [1, 1], [1, 3, 5, 1, 2], [1, 2, 3, 5, 1], [2, 4, 5, 1], [1, 1, 1, 5, 1, 2], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 2 (![false, false, true])]

  right
  refine ⟨30, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original30_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen24 2 (![false, false, true]))) original30
    (![[0], [1], [], [0, 3, 4, 6, 7], [1, 1, 1], [7]])
    (![[0], [1], [0, 0], [0, 0, 0, 4, 0, 1], [0, 0, 0, 4, 3, 1], [1, 1, 5], [0, 1, 3, 0, 4, 3], [5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 0 (![true, false, true])]

  right
  refine ⟨38, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original38_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen24 0 (![true, false, true]))) original38
    (![[], [1, 6], [4, 0, 2, 3], [2, 3, 5], [1, 1, 3, 1], [3, 0, 5]])
    (![[1, 5, 1], [1, 1, 5, 4, 2], [1, 1, 1, 3, 4], [2, 4, 1, 5], [1, 2, 1, 2, 3], [1, 2, 1, 5, 1, 4], [1, 5, 4, 2], [2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 1 (![false, true, true])]

  right
  refine ⟨46, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original46_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen24 1 (![false, true, true]))) original46
    (![[1], [], [0, 5, 7], [1, 3], [5, 7], [0, 5, 7]])
    (![[2, 4], [0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 2, 0, 2], [2, 2, 4], [0, 2, 0, 3, 2, 3, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge24_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen24 0 (![true, true, true])]

  right
  refine ⟨46, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original46_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen24 0 (![true, true, true]))) original46
    (![[], [1, 2], [1, 2, 0], [2, 3, 6], [5, 1, 6], [0, 1]])
    (![[5, 1], [1, 1, 1], [1, 1], [1, 3, 5, 4, 5], [1, 2, 2, 1], [2, 1, 2, 1], [1, 1, 1, 5, 4, 5], [2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem checks24 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen24 (gen24 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge24_1⟩

  · exact Or.inr ⟨1, by decide, edge24_2⟩

  · exact Or.inr ⟨0, by decide, edge24_3⟩

  · exact Or.inr ⟨2, by decide, edge24_4⟩

  · exact Or.inr ⟨0, by decide, edge24_5⟩

  · exact Or.inr ⟨1, by decide, edge24_6⟩

  · exact Or.inr ⟨0, by decide, edge24_7⟩

private theorem step24 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 24)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 24 gen24 gen24_eq checks24 H hm hp

private def gen25 : Fin 4 → SylowModel := ![rootOne ^ 3, root 6, root 2 * root 4 * root 8, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9]

private theorem gen25_eq : Subgroup.closure (Set.range gen25) = smallParityCensusNode 25 := by
  rw [← original25_eq]
  exact closure_eq_words gen25 original25
    (![[1], [5, 6, 7], [0], [2]])
    (![[2], [0], [3], [0, 0], [0, 3, 1, 0, 0, 0, 3], [2, 2, 3, 1, 3], [2, 2, 3, 3], [1, 3, 1, 3, 3, 3], [2, 3, 2, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, false, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, false, false, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen25 0 (![true, false, false, false])) k ∈ character.ker) k

private theorem edge25_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 1) (![false, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 1 (![false, true, false, false])]

  right
  refine ⟨55, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original55_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 1 (![false, true, false, false]))) original55
    (![[1], [], [0], [2], [6, 1], [], [0], [2, 5, 7]])
    (![[2], [0], [3], [0, 0], [0, 0, 3, 4, 7, 4], [2, 2], [0, 0, 4, 0], [0, 0, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, true, false, false])]

  right
  refine ⟨55, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original55_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, true, false, false]))) original55
    (![[], [1, 3, 4, 5], [0, 2, 2], [2, 5, 7], [3], [4, 1, 5], [0, 2, 2], [2, 4, 6]])
    (![[2, 3, 3], [3, 5, 3], [1, 7, 5], [4], [7, 3], [2, 2], [1, 4, 1], [1, 3, 5, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 2) (![false, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 2 (![false, false, true, false])]

  right
  refine ⟨31, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original31_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 2 (![false, false, true, false]))) original31
    (![[0], [4, 5, 6], [], [1], [0], [4, 5, 6], [6, 7], [1, 5, 7]])
    (![[0], [3], [0, 0], [0, 0, 0, 3, 0, 1, 3], [3, 1, 3, 6], [3, 3, 6], [3, 7], [3, 6, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, false, true, false])]

  right
  refine ⟨37, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original37_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, false, true, false]))) original37
    (![[], [4, 5, 6], [0, 1, 3, 1, 2], [1, 1, 1, 4], [2, 6, 7], [4, 6], [3, 0, 5], [1, 3]])
    (![[1, 7, 3, 6], [2, 6, 3, 1], [2, 2], [3, 7, 5], [1, 7, 7], [1, 5], [1, 5, 7, 7], [1, 3, 5, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 1) (![false, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 1 (![false, true, true, false])]

  right
  refine ⟨57, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original57_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 1 (![false, true, true, false]))) original57
    (![[1], [], [0, 2, 2, 7], [2], [6, 1], [], [0, 2, 2, 7], [2, 5, 7]])
    (![[2, 2, 2, 3, 7], [0], [3], [0, 0], [0, 0, 3, 4, 7, 4], [2, 2], [0, 0, 4, 0], [0, 0, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, true, true, false])]

  right
  refine ⟨57, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original57_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, true, true, false]))) original57
    (![[], [1, 3, 4, 5], [0, 1, 3, 4], [2, 5, 7], [3], [4, 1, 5], [4, 1, 0], [2, 4, 6]])
    (![[1, 2, 2, 2], [3, 5, 3], [1, 7, 5], [4], [7, 3], [2, 6], [1, 4, 1], [1, 3, 5, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_8 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 3) (![false, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 3 (![false, false, false, true])]

  right
  refine ⟨45, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original45_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 3 (![false, false, false, true]))) original45
    (![[1], [2, 5, 7], [0], [], [1, 2, 4, 6], [0, 0, 2, 5], [0, 5, 6], [5]])
    (![[2], [0], [1, 2, 6], [0, 0], [0, 0, 4, 0, 1], [7], [1, 5], [2, 6, 7]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_9 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, false, false, true])]

  right
  refine ⟨50, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original50_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, false, false, true]))) original50
    (![[], [0, 0, 2, 5], [0, 2, 5], [1, 3, 7], [3, 2, 4], [2, 6], [0, 2, 5], [1, 5, 6]])
    (![[1, 2, 2, 2], [1, 7, 1], [1, 7, 3], [1, 3, 3, 1], [3, 4, 5, 3], [1, 3, 5, 7], [1, 5, 7, 3], [1, 4, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_10 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 1) (![false, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 1 (![false, true, false, true])]

  right
  refine ⟨56, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original56_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 1 (![false, true, false, true]))) original56
    (![[1], [], [0], [0, 2, 0], [6, 1], [], [0], [2, 6]])
    (![[2], [0], [2, 3, 2], [0, 0], [0, 0, 3, 0, 3, 4], [2, 2], [0, 0, 4, 0], [0, 0, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_11 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, true, false, true])]

  right
  refine ⟨56, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original56_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, true, false, true]))) original56
    (![[], [1, 3, 4, 5], [0, 5, 6], [1, 2, 3, 7], [3], [4, 1, 5], [0, 5, 6], [1, 4, 2, 5]])
    (![[2, 3, 7], [7, 5, 3], [5, 4, 7], [4], [7, 4, 7], [2, 2], [1, 4, 1], [1, 4, 5, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_12 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 2) (![false, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 2 (![false, false, true, true])]

  right
  refine ⟨41, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original41_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 2 (![false, false, true, true]))) original41
    (![[1], [4, 5, 6], [], [0, 7], [1], [4, 5, 6], [6, 7], [0, 5, 6, 7]])
    (![[3, 3, 3], [0], [0, 0], [0, 0, 0, 1, 3, 0, 3], [3, 1, 6, 7], [3, 6, 7], [3, 3, 6], [3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_13 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, false, true, true])]

  right
  refine ⟨42, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original42_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, false, true, true]))) original42
    (![[], [4, 5], [1, 3, 0, 2], [1, 4, 2], [2, 3, 6], [4, 6], [1, 0], [5, 1]])
    (![[3, 6], [1, 7, 1], [7, 1, 7], [1, 7, 4, 7], [1, 7, 3], [7, 3], [1, 5, 7, 3], [1, 4, 1, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_14 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 1) (![false, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 1 (![false, true, true, true])]

  right
  refine ⟨58, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original58_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen25 1 (![false, true, true, true]))) original58
    (![[1], [], [0, 2, 2, 5], [2, 2, 2, 5], [6, 1], [], [0, 2, 2, 5], [2, 6]])
    (![[2, 2, 2, 3, 3], [0], [2, 7, 2], [0, 0], [0, 0, 3, 0, 3, 4], [2, 2], [0, 0, 4, 0], [0, 0, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge25_15 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 0) (![true, true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen25 0 (![true, true, true, true])]

  right
  refine ⟨58, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original58_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen25 0 (![true, true, true, true]))) original58
    (![[], [1, 3, 4, 5], [0, 1, 3, 4], [1, 2, 3, 7], [3], [4, 1, 5], [4, 1, 0], [1, 4, 2, 5]])
    (![[1, 2, 2, 2], [7, 5, 3], [5, 4, 7], [4], [7, 4, 7], [2, 6], [1, 4, 1], [1, 4, 5, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem checks25 (σ : Fin 4 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen25 (gen25 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true] := by
    exact (by decide : ∀ σ : Fin 4 → Bool, σ = ![false, false, false, false] ∨ σ = ![true, false, false, false] ∨ σ = ![false, true, false, false] ∨ σ = ![true, true, false, false] ∨ σ = ![false, false, true, false] ∨ σ = ![true, false, true, false] ∨ σ = ![false, true, true, false] ∨ σ = ![true, true, true, false] ∨ σ = ![false, false, false, true] ∨ σ = ![true, false, false, true] ∨ σ = ![false, true, false, true] ∨ σ = ![true, true, false, true] ∨ σ = ![false, false, true, true] ∨ σ = ![true, false, true, true] ∨ σ = ![false, true, true, true] ∨ σ = ![true, true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge25_1⟩

  · exact Or.inr ⟨1, by decide, edge25_2⟩

  · exact Or.inr ⟨0, by decide, edge25_3⟩

  · exact Or.inr ⟨2, by decide, edge25_4⟩

  · exact Or.inr ⟨0, by decide, edge25_5⟩

  · exact Or.inr ⟨1, by decide, edge25_6⟩

  · exact Or.inr ⟨0, by decide, edge25_7⟩

  · exact Or.inr ⟨3, by decide, edge25_8⟩

  · exact Or.inr ⟨0, by decide, edge25_9⟩

  · exact Or.inr ⟨1, by decide, edge25_10⟩

  · exact Or.inr ⟨0, by decide, edge25_11⟩

  · exact Or.inr ⟨2, by decide, edge25_12⟩

  · exact Or.inr ⟨0, by decide, edge25_13⟩

  · exact Or.inr ⟨1, by decide, edge25_14⟩

  · exact Or.inr ⟨0, by decide, edge25_15⟩

private theorem step25 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 25)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 25 gen25 gen25_eq checks25 H hm hp

private def gen26 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, rootOne ^ 3 * root 5 * root 8, root 3 * root 5 * root 8]

private theorem gen26_eq : Subgroup.closure (Set.range gen26) = smallParityCensusNode 26 := by
  rw [← original26_eq]
  exact closure_eq_words gen26 original26
    (![[2], [1], [0]])
    (![[2], [1], [0], [0, 1, 0, 1, 1, 1, 2, 1, 2, 1], [0, 0, 0, 1, 1, 1, 0, 1], [0, 1, 0, 1, 2, 1, 2, 1], [0, 0, 2, 2], [0, 0, 1, 0, 1, 1, 0, 1], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 0 (![true, false, false])]

  right
  refine ⟨42, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original42_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen26 0 (![true, false, false]))) original42
    (![[], [1], [0], [5, 7], [1, 3], [0, 5, 7]])
    (![[2], [1], [1, 1, 1, 2, 1, 1, 4, 5], [1, 1, 1, 2, 2, 4], [1, 2, 1, 1, 4, 5], [2, 5], [1, 1, 2, 2, 4, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 1 (![false, true, false])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen26 1 (![false, true, false])) k ∈ character.ker) k

private theorem edge26_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 0 (![true, true, false])]

  right
  refine ⟨42, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original42_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen26 0 (![true, true, false]))) original42
    (![[], [1, 6], [0, 6], [5, 6, 7], [1, 3], [0, 5, 7]])
    (![[1, 1, 5, 4, 4], [1, 1, 1, 2, 2, 4, 4], [1, 5, 4, 5], [1, 1, 2, 2, 4, 1], [1, 1, 1, 2, 4, 2], [1, 1, 3, 4, 4], [1, 1, 2, 2, 4, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 2 (![false, false, true])]

  right
  refine ⟨32, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original32_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen26 2 (![false, false, true]))) original32
    (![[1], [0], [], [1, 1, 1], [0, 3, 4, 7], [7]])
    (![[1], [0], [0, 1, 0, 1, 1, 4, 4, 4], [0, 1, 0, 1, 4, 4], [0, 1, 0, 4, 4, 4], [0, 0, 5], [0, 0, 1, 1, 4, 4], [5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 0 (![true, false, true])]

  right
  refine ⟨47, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original47_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen26 0 (![true, false, true]))) original47
    (![[], [4, 1, 7], [0, 4], [5, 6, 7], [3, 1, 4], [0, 4]])
    (![[1, 4, 4, 2, 1], [1, 2, 4, 2, 1, 4, 1], [1, 2, 4, 2, 3], [1, 1, 3, 4, 1], [1, 2, 1, 2, 4, 4], [1, 1, 3, 4, 4], [1, 1, 2, 2, 4, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 1 (![false, true, true])]

  right
  refine ⟨36, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original36_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen26 1 (![false, true, true]))) original36
    (![[1, 6], [], [0, 2, 3, 5], [1, 3, 5], [0, 4, 0, 3], [3, 0, 5]])
    (![[0, 3, 4, 5, 4], [2, 5, 4, 0, 4], [2, 2], [3, 0], [0, 3, 2, 4, 2], [0, 4, 0, 4], [0, 0, 3, 4, 3, 4], [2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge26_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen26 0 (![true, true, true])]

  right
  refine ⟨47, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original47_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen26 0 (![true, true, true]))) original47
    (![[], [5, 1], [0, 5, 7], [5, 7], [1, 3, 7], [0, 5, 7]])
    (![[2, 3], [1, 3], [1, 1, 2, 1, 2, 1, 4, 1], [1, 1, 1, 4, 3], [1, 2, 1, 4, 4, 2], [2, 2, 3], [1, 1, 2, 2, 4, 4], [2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks26 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen26 (gen26 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge26_1⟩

  · exact Or.inr ⟨1, by decide, edge26_2⟩

  · exact Or.inr ⟨0, by decide, edge26_3⟩

  · exact Or.inr ⟨2, by decide, edge26_4⟩

  · exact Or.inr ⟨0, by decide, edge26_5⟩

  · exact Or.inr ⟨1, by decide, edge26_6⟩

  · exact Or.inr ⟨0, by decide, edge26_7⟩

private theorem step26 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 26)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 26 gen26 gen26_eq checks26 H hm hp

private def gen27 : Fin 2 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]

private theorem gen27_eq : Subgroup.closure (Set.range gen27) = smallParityCensusNode 27 := by
  rw [← original27_eq]
  exact closure_eq_words gen27 original27
    (![[0], [1]])
    (![[0], [1], [0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]])
    (by decide +kernel) (by decide +kernel)

private theorem edge27_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen27 (gen27 0) (![true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen27 0 (![true, false])]

  right
  refine ⟨34, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original34_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen27 0 (![true, false]))) original34
    (![[], [0], [3, 2, 1, 4], [0, 2, 3, 5]])
    (![[1], [1, 1], [2, 3, 3], [1, 1, 1, 1], [1, 2, 2, 3, 2], [1, 2, 2, 1, 1, 1], [2, 2, 2, 3, 1], [2, 2, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge27_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen27 (gen27 1) (![false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen27 1 (![false, true])]

  right
  refine ⟨33, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original33_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen27 1 (![false, true]))) original33
    (![[0], [], [0, 3, 2, 6], [0, 3, 2, 0]])
    (![[0], [0, 0], [3, 3, 2, 3, 3, 2, 3], [0, 0, 0, 0], [0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 3, 0], [2, 0, 3, 3, 3], [3, 3, 3, 3]])
    (by decide +kernel) (by decide +kernel)

private theorem edge27_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen27 (gen27 0) (![true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen27 0 (![true, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen27 0 (![true, true])) k ∈ character.ker) k

private theorem checks27 (σ : Fin 2 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen27 (gen27 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true] := by
    exact (by decide : ∀ σ : Fin 2 → Bool, σ = ![false, false] ∨ σ = ![true, false] ∨ σ = ![false, true] ∨ σ = ![true, true]) σ
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge27_1⟩

  · exact Or.inr ⟨1, by decide, edge27_2⟩

  · exact Or.inr ⟨0, by decide, edge27_3⟩

private theorem step27 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 27)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 27 gen27 gen27_eq checks27 H hm hp

private def gen28 : Fin 3 → SylowModel := ![root 4 * root 7 * root 8, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9]

private theorem gen28_eq : Subgroup.closure (Set.range gen28) = smallParityCensusNode 28 := by
  rw [← original28_eq]
  exact closure_eq_words gen28 original28
    (![[0, 4, 3, 0, 2], [0], [1]])
    (![[1], [2], [1, 1], [1, 0, 1, 1, 2, 1, 2, 1, 1], [1, 1, 1, 1], [0, 1, 1, 0, 2, 2], [0, 1, 0, 1, 2, 2], [0, 2, 2, 1, 0, 1], [0, 1, 1, 2, 0, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_1 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 0) (![true, false, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 0 (![true, false, false])]

  right
  refine ⟨59, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original59_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen28 0 (![true, false, false]))) original59
    (![[], [0], [1], [], [3, 5, 0], [6, 1, 3]])
    (![[1], [2], [1, 1], [1, 4, 2, 5], [1, 1, 1, 1], [1, 1, 5, 2], [1, 5, 5, 4], [1, 1, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_2 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 1) (![false, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 1 (![false, true, false])]

  right
  refine ⟨34, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original34_eq]
  exact closure_eq_words ((MulAut.conj (root 1 * root 3 * root 5 * root 6 * root 7 * root 9)).toMonoidHom ∘ (flatSchreier gen28 1 (![false, true, false]))) original34
    (![[2, 5, 6, 7], [], [3, 4, 0], [2, 4, 6], [3, 4, 1, 5], [0, 7]])
    (![[0, 2, 4, 0, 4], [5, 5], [2, 4, 0, 2], [5, 5, 5, 5], [5, 4, 5], [0, 2, 2, 4, 3], [0, 3, 5, 5, 4], [4, 4, 4, 4]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_3 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 0) (![true, true, false])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 0 (![true, true, false])]

  right
  refine ⟨60, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original60_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen28 0 (![true, true, false]))) original60
    (![[], [0, 6], [3, 1, 7], [], [0, 3], [5, 1, 7]])
    (![[1, 1, 2, 2, 1], [1, 1, 2, 5, 2], [1, 1, 1, 4, 2, 5], [1, 2, 2, 4], [1, 1, 1, 1], [1, 4, 5, 2], [1, 2, 2, 1], [1, 4, 2, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_4 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 2) (![false, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 2 (![false, false, true])]

  right
  refine ⟨33, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original33_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen28 2 (![false, false, true]))) original33
    (![[2, 6, 7], [0], [], [2, 4, 5], [3, 4, 0], [1, 3, 4, 7]])
    (![[1], [1, 1], [1, 5, 1, 3], [1, 5, 4], [1, 1, 5], [1, 1, 0, 3, 5], [0, 1, 0, 5, 1], [5, 5, 5, 5]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_5 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 0) (![true, false, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 0 (![true, false, true])]

  right
  refine ⟨60, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original60_eq]
  exact closure_eq_words ((MulAut.conj (1)).toMonoidHom ∘ (flatSchreier gen28 0 (![true, false, true]))) original60
    (![[], [0], [6, 1, 3], [], [3, 5, 0], [1]])
    (![[1], [5], [1, 1], [1, 4, 2, 2], [1, 1, 1, 1], [1, 1, 5, 5], [1, 5, 2, 4], [1, 1, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem edge28_6 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 1) (![false, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 1 (![false, true, true])]

  left
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact (by decide +kernel : ∀ k, (flatSchreier gen28 1 (![false, true, true])) k ∈ character.ker) k

private theorem edge28_7 :
    let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 0) (![true, true, true])))
    L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  dsimp only
  rw [← flat_range gen28 0 (![true, true, true])]

  right
  refine ⟨59, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, ← original59_eq]
  exact closure_eq_words ((MulAut.conj (root 2 * root 3 * root 4 * root 7)).toMonoidHom ∘ (flatSchreier gen28 0 (![true, true, true]))) original59
    (![[], [0, 6], [1, 5, 7], [], [0, 3], [3, 6, 1]])
    (![[1, 1, 2, 5, 1], [1, 1, 1, 5, 1], [1, 1, 1, 4, 2, 2], [1, 2, 5, 4], [1, 1, 1, 1], [1, 4, 5, 5], [1, 2, 5, 1], [1, 4, 2, 2]])
    (by decide +kernel) (by decide +kernel)

private theorem checks28 (σ : Fin 3 → Bool) :
    (∀ j, σ j = false) ∨ ∃ j, σ j = true ∧
      let L := Subgroup.closure (Set.range (binarySchreierGenerator gen28 (gen28 j) σ))
      L ≤ character.ker ∨ Represented smallParityCensusNode L := by
  have h : σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true] := by
    exact (by decide : ∀ σ : Fin 3 → Bool, σ = ![false, false, false] ∨ σ = ![true, false, false] ∨ σ = ![false, true, false] ∨ σ = ![true, true, false] ∨ σ = ![false, false, true] ∨ σ = ![true, false, true] ∨ σ = ![false, true, true] ∨ σ = ![true, true, true]) σ
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)

  · exact Or.inr ⟨0, by decide, edge28_1⟩

  · exact Or.inr ⟨1, by decide, edge28_2⟩

  · exact Or.inr ⟨0, by decide, edge28_3⟩

  · exact Or.inr ⟨2, by decide, edge28_4⟩

  · exact Or.inr ⟨0, by decide, edge28_5⟩

  · exact Or.inr ⟨1, by decide, edge28_6⟩

  · exact Or.inr ⟨0, by decide, edge28_7⟩

private theorem step28 (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode 28)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H :=
  chosen_binary 28 gen28 gen28_eq checks28 H hm hp


/-- Maximal-step coverage for the first twenty-nine fixed parity census nodes. -/
public theorem smallParityCensusStep_upper (i : Fin 131) (hi : i.val < 29)
    (H : Subgroup SylowModel) (hm : H ⋖ smallParityCensusNode i)
    (_hc : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hp : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0 H hm hp
  · exact step1 H hm hp
  · exact step2 H hm hp
  · exact step3 H hm hp
  · exact step4 H hm hp
  · exact step5 H hm hp
  · exact step6 H hm hp
  · exact step7 H hm hp
  · exact step8 H hm hp
  · exact step9 H hm hp
  · exact step10 H hm hp
  · exact step11 H hm hp
  · exact step12 H hm hp
  · exact step13 H hm hp
  · exact step14 H hm hp
  · exact step15 H hm hp
  · exact step16 H hm hp
  · exact step17 H hm hp
  · exact step18 H hm hp
  · exact step19 H hm hp
  · exact step20 H hm hp
  · exact step21 H hm hp
  · exact step22 H hm hp
  · exact step23 H hm hp
  · exact step24 H hm hp
  · exact step25 H hm hp
  · exact step26 H hm hp
  · exact step27 H hm hp
  · exact step28 H hm hp

end ReeTwo.SylowModel
