module

public import Stellmacher.Recognition.GTwoSixtyFourFusion
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Exclusion of the order-64 G₂ local configuration

A finite nonsolvable simple N₂ group with trivial odd cores in its two-local
subgroups cannot have both the actual G₂ local type and a Sylow two-subgroup
of order 64.

The ambient fusion theorem supplies an index-two subgroup of the Sylow group
and an involution with no ambient conjugate in that subgroup. Thompson transfer
contradicts this separation: simplicity and the Sylow order rule out a normal
subgroup of index two in the ambient group. Nonsolvability is retained in the
recognition interface, although the Sylow order suffices for this last step.

Source: Stellmacher (8.6)(a) and its subsequent local-type definition,
`refs/latex/stellmacher-n-group.tex`; Thompson transfer is proved in
`Theory.GroupTheory.InvolutionTransfer`.
-/

namespace Stellmacher.Recognition

/-- The order-64 branch of the actual G₂ local type is impossible in a simple
N₂ group whose two-local subgroups have trivial odd cores. -/
public theorem gTwo_card64_exclusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (hType : IsOfGTwoTwoDerivedType G) (S : Sylow 2 G)
    (hcard : Nat.card S = 64) : False := by
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hnormal hindex
    rcases hnormal.eq_bot_or_eq_top with rfl | rfl
    · rw [Subgroup.index_bot] at hindex
      have hdiv := (S : Subgroup G).card_subgroup_dvd_card
      rw [hcard, hindex] at hdiv
      norm_num at hdiv
    · simp at hindex
  obtain ⟨U, t, hU, ht, hsep⟩ := gTwo_card64_fusion_separation S hN hcore hType hcard
  obtain ⟨u, htu, hu⟩ := S.exists_isConj_mem_of_index_two hno U hU t ht
  exact hsep u hu htu

end Stellmacher.Recognition
