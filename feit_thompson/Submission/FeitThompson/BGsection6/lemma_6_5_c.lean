/-
Authors: OpenAI, Yusen Tang
-/

module

public import Submission.FeitThompson.BGsection6.lemma_6_5_b

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.5(c) from BG Section 6 -/

public theorem lemma_6_5_c
    {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {K U H : Subgroup G} [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (g : G) (hconj : H.conjBy g ≤ U) :
    ∃ c ∈ subgroupCentralizerIn K H, ∃ u ∈ U, g = u * c := by
  exact lemma_6_5_c_core (K := K) (U := U) (H := H) hKU hHU hcop g hconj

