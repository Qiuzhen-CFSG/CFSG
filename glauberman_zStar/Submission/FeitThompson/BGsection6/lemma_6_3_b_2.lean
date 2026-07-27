/-
Authors: OpenAI, Yusen Tang
-/

module

public import Submission.FeitThompson.BGsection6.lemma_6_3_b_1

open scoped MatrixGroups Pointwise TensorProduct

/-! # lemma_6_3_b_2 from BG Section 6 -/

public theorem lemma_6_3_b_2
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hdn : Group.IsNilpotent (derivedSubgroup G))
    (hip : (Nat.card (G ⧸ derivedSubgroup G)).Prime)
    {K : Subgroup G} (hCompl : IsCompl (derivedSubgroup G) K) :
    derivedSubgroup G = ⁅(⊤ : Subgroup G), K⁆ := by
  rcases lemma_6_3_b_1 (G := G) hdn hip with ⟨π, hHallπ⟩
  have hcomm :
      derivedSubgroup G = ⁅derivedSubgroup G, K⁆ :=
    lemma_6_3_a_1 (G := G) (H := derivedSubgroup G) ⟨π, hHallπ⟩ hCompl le_rfl
  apply le_antisymm
  · rw [hcomm]
    exact Subgroup.commutator_mono le_top le_rfl
  · change ⁅(⊤ : Subgroup G), K⁆ ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    exact Subgroup.commutator_mono le_rfl le_top
