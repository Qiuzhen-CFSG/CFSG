module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The order forced by a self-centralizing extraspecial two-core

In a nonsolvable finite group, a self-centralizing extraspecial two-core of
elementary rank at most two has order thirty-two. The rank-two extraspecial
classification bounds its order by thirty-two and leaves eight as the only
smaller possibility. At order eight its Frattini quotient has four elements.
The exact Frattini-action kernel is the two-core, so the whole group would be
an extension of solvable groups.

This intrinsic argument supplies the order clause in the nontrivial-two-core
branch for Sp₄(3); it does not establish extraspeciality, the rank bound, or
self-centralization. Source application: Aschbacher–Smith, Theorem 0.1.2(4),
condition K, printed pp.4 and 482 of `refs/quasithin.pdf`. The rank-two
extraspecial classification is documented in the imported group-theory modules.
-/

namespace Matrix.PSp4Three.NontrivialTwoCore

open Subgroup

/-- Nonsolvability excludes the order-eight self-centralizing extraspecial
core, leaving order thirty-two under the elementary-rank bound. -/
public theorem card_eq_thirty_two_of_extraspecial_rank_two
    {G : Type*} [Group G] [Finite G]
    (hnsolv : ¬ Group.IsSolvable G)
    [IsExtraspecial 2 (pCore 2 G)]
    (hrank : ∀ E : Subgroup (pCore 2 G), IsElementaryAbelian 2 E → Nat.card E < 8)
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Nat.card (pCore 2 G) = 32 := by
  have hbound := IsExtraspecial.card_le_thirty_two_of_rank_two hrank
  rcases IsExtraspecial.card_eq_eight_or_thirty_two_le (P := pCore 2 G) with hsmall | hlarge
  · exfalso
    apply hnsolv
    let Q := pCore 2 G
    let V := Q ⧸ frattini Q
    have hV : Nat.card V = 4 := by
      have hc := card_eq_card_quotient_mul_card_subgroup (center Q)
      rw [show Nat.card Q = 8 from hsmall, IsExtraspecial.center_order_p 2 Q] at hc
      change Nat.card (Q ⧸ frattini Q) = 4
      rw [IsExtraspecial.frattini_eq_center_two]
      omega
    let e : V ≃ Fin 4 := Finite.equivFinOfCardEq hV
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm V) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Equiv.permCongrHom e).toMonoidHom) (Equiv.permCongrHom e).injective
    let : Group.IsSolvable (MulAut V) :=
      Group.isSolvable_of_isSolvable_injective
        (f := MulAut.toPerm V) (fun _ _ h => MulEquiv.toEquiv_injective h)
    let a : G →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
    have hk : a.ker = Q := pCore_frattini_action_kernel 2 hcentral
    let : Group.IsNilpotent Q := pCore_isNilpotent
    exact Group.isSolvable_of_ker_le_range Q.subtype a (by rw [hk, range_subtype])
  · omega

end Matrix.PSp4Three.NontrivialTwoCore
