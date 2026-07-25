/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFchapter4section2.claim_16_a

namespace BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (16), second clause -/

/-- The field involution acts by inversion on the generator `beta` of `W`. -/
public theorem claim_16_b
    (E : Type*) [Field E] (W : Subgroup Eˣ) (betaUnit : Eˣ)
    (sigma : E ≃+* E)
    (hbeta_generator : Subgroup.closure ({betaUnit} : Set Eˣ) = W)
    (hsigma_W : ∀ a : Eˣ, a ∈ W → sigma (a : E) = (a : E)⁻¹) :
    sigma (betaUnit : E) = (betaUnit : E)⁻¹ := by
  have hmem : betaUnit ∈ W := by
    rw [← hbeta_generator]
    exact Subgroup.subset_closure (Set.mem_singleton betaUnit)
  exact hsigma_W betaUnit hmem

end PFchapter4section2
end BenderSuzuki
