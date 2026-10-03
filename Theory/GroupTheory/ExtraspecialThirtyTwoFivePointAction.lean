module

public import Theory.GroupTheory.FrattiniInvolutionPoints
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoInvolutionPointCardinality
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoInvolutionPointGeneration

/-!
# Five-point actions from the involution geometry of a two-core

The five nonzero singular vectors of the minus-type extraspecial group of
order 32 are intrinsically the nonidentity Frattini cosets admitting
square-one representatives. The elementary-rank bound on the core gives
exactly five such points, and they generate its Frattini quotient. Restricting
the Frattini action to these points therefore preserves its kernel, which is
exactly the self-centralizing two-core.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Subgroup

/-- The cardinality and generation statements for the intrinsic involution
points suffice for the faithful five-point action modulo a two-core. -/
public theorem pCore_exists_five_point_action_of_involution_points
    {K : Type*} [Group K] [Finite K]
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (frattiniInvolutionPoints (pCore 2 K)) = 5)
    (hgen : closure (frattiniInvolutionPoints (pCore 2 K)) = ⊤) :
    ∃ f : K →* Equiv.Perm (Fin 5), f.ker = pCore 2 K :=
  pCore_exists_perm_action_of_frattiniInvolutionPoints hcentral hcard hgen

/-- A self-centralizing extraspecial two-core of order 32 with elementary rank
at most two is the exact kernel of a five-point permutation action. -/
public theorem pCore_exists_five_point_action_of_extraspecial_card_thirty_two
    {K : Type*} [Group K] [Finite K] [IsExtraspecial 2 (pCore 2 K)]
    (hrank : ∀ E : Subgroup (pCore 2 K), IsElementaryAbelian 2 E → Nat.card E < 8)
    (hcard : Nat.card (pCore 2 K) = 32)
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    ∃ f : K →* Equiv.Perm (Fin 5), f.ker = pCore 2 K :=
  pCore_exists_five_point_action_of_involution_points hcentral
    (IsExtraspecial.card_frattiniInvolutionPoints_of_card_thirty_two hrank hcard)
    (IsExtraspecial.closure_frattiniInvolutionPoints_eq_top_of_card_thirty_two hrank hcard)

end Subgroup
