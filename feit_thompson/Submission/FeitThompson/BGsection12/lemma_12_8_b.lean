/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.BGsection12.lemma_12_8_a

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.8(b). -/
public theorem lemma_12_8_b
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    IsHallSubgroup (section12Tau2Primes M) E₂ := by
  exact
    section12_E2_global_hall_of_abelian_sylow_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm


end Section12
