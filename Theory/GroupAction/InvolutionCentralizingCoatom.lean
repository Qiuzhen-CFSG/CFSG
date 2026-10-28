module

public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.GroupTheory.SubgroupConjugation

/-!
# An involution centralizing a coatom has displacement at most two

The coatom embeds into the fixed subgroup of the literal conjugation action.
Involution rank-nullity bounds its displacement, and the injective inclusion
of the module identifies that displacement with the ambient commutator.
The hypotheses use the actual normalizing action and a supplied centralizing
subgroup, not an assumed displacement bound.

This elementary count supplies the transvection step in Stellmacher (9.10)(2),
printed p.57 of `refs/files/stellmacher-n-group.pdf`; it is independent of the
coset graph and of the classification hypotheses.
-/

namespace Subgroup

universe u

public theorem commutator_card_le_two_of_centralizing_index_two
    {G : Type u} [Group G] [Finite G]
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (actor : G) (hactor : actor ≠ 1 ∧ actor ^ 2 = 1)
    (hnormal : zpowers actor ≤ normalizer (U : Set G))
    (hKU : K ≤ U) (hindex : Nat.card U = 2 * Nat.card K)
    (hcentral : K ≤ centralizer (zpowers actor : Set G)) :
    Nat.card (⁅U, zpowers actor⁆ : Subgroup G) ≤ 2 := by
  let actors := zpowers actor
  let _ : Subgroup.Normalizes actors U := ⟨hnormal⟩
  let generator : actors := ⟨actor, mem_zpowers actor⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hactor.1 (congrArg Subtype.val heq), Subtype.ext hactor.2⟩
  have hactors : Nat.card actors = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hactor.2 hactor.1]
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega)
  have hfixed : K.subgroupOf U ≤ FixedPoints.subgroup actors U := by
    intro point hpoint
    rw [FixedPoints.mem_subgroup]
    intro mover
    apply Subtype.ext
    change (mover : G) * (point : G) * (mover : G)⁻¹ = (point : G)
    have hcomm := mem_centralizer_iff.mp (hcentral hpoint) (mover : G) mover.property
    change (mover : G) * (point : G) = (point : G) * (mover : G) at hcomm
    rw [hcomm, mul_inv_cancel_right]
  have hfixedCard : Nat.card K ≤ Nat.card (FixedPoints.subgroup actors U) := by
    have hh := card_le_of_le hfixed
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKU).toEquiv] at hh
  have hcount := (card_two_action_fixed_commutator_card_data
    (U := U) generator hgenerator hactors).1
  have hpositive : 0 < Nat.card (FixedPoints.subgroup actors U) := Nat.card_pos
  have hbound : Nat.card (commutatorAction actors U) ≤ 2 := by
    nlinarith
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator U actors hnormal
  rw [← hmap, card_map_of_injective U.subtype_injective]
  exact hbound

end Subgroup
