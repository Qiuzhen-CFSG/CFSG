module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# The surviving binary-block configuration in 1.3.8

This interface is the intermediate conclusion to be constructed by the C.2.7
model exclusions. It retains the actual natural-module model of K, its
subnormality in H, the Sylow condition, and the action of R = O₂(XT).
It assumes no commutation, residual decomposition, or Krull–Schmidt conclusion.
The independent final argument must construct those from this interface.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding

variable {G : Type*} [Group G]

/-- The binary case remaining after pushing up. This is a conclusion contract,
not an additional assumption in the radical exclusion theorem. -/
structure BinaryBlockEmbedding (p : ℕ) (T X P H₀ K : Subgroup G) : Prop where
  local_input : LocalInput p T X P H₀
  sylow_two : IsSylowIn 2 T H₀
  component : K ∈ cComponentsIn H₀
  quasisimple : IsQuasisimple (XiQuotient K)
  plane : Nonempty (P ≃* Plane p)
  swapped : SwappedFactors T P K
  source_model : SwappedModel p (XiQuotient K)
  containment : X ≤ componentOrbit K T
  radical_normalizes : (X ⊔ T).pCoreIn 2 ≤ normalizer K
  block : ChapterC.IsBlock (K.subgroupOf H₀)
  binary_type : ∃ n : ℕ, ChapterC.IsL2EvenBlock K n

/-- The subgroup W on p.514 uses the two-residual O², not the two-core O₂. -/
def blockResidual (X K : Subgroup G) : Subgroup G :=
  (pResidual 2 (X ⊓ K : Subgroup G)).map (X ⊓ K).subtype

/-- W lies in the specified intersection. -/
theorem blockResidual_le (X K : Subgroup G) : blockResidual X K ≤ X ⊓ K :=
  map_subtype_le _

/-- W is two-perfect, independently of the still-needed block decomposition. -/
theorem blockResidual_isPPerfect [Finite G] (X K : Subgroup G) :
    IsPPerfect 2 (blockResidual X K) := isPPerfect_embedded_pResidual 2 (X ⊓ K)

end CFSG.Quasithin.Chapter1.RadicalExclusions
