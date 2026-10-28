module
public import Theory.GroupAction.SwappedSupportCommutatorLowerBound
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# Large two-group displacement on the sixteen-point canonical module

In a faithful one-seven action on an elementary group of order sixteen,
let a two-subgroup have order greater than four and contain a rank-one actor
in a supplied canonical factor. Its full displacement has cardinal at least
eight. All groups and actors belong to the original action.

A two-subgroup preserving one order-four canonical support has order at most
four. Thus the retained two-subgroup contains an actor carrying that support
to a distinct, disjoint canonical support. The difference map on the first
support has order-four image disjoint from the rank-one line. Their join has
order eight and lies in the full two-subgroup displacement.

This is the natural wreath Sylow calculation used in Stellmacher (9.10)(10)
and (12), printed pp.58–59.
-/
namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_large_two_group_commutator_card_ge_eight
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (D S : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (hS : IsPGroup 2 S)
    (hV : Nat.card V = 16) (hlarge : 4 < Nat.card S)
    (a : K) (haD : a ∈ D) (haS : a ∈ S)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2) :
    8 ≤ Nat.card (commutatorAction S V) := by
  obtain ⟨c, hmove, _⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D S hD hS hV hlarge
  let E := D.conjBy (c : K)
  have hE := hD.conjBy D (c : K)
  have hmap : (commutatorAction D V).map
      (MulDistribMulAction.toMulAut K V (c : K)).toMonoidHom = commutatorAction E V :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D (c : K)
  have hDE : D ≠ E := by
    intro heq
    apply hmove
    rw [hmap, ← heq]
  have hdisjoint : Disjoint (commutatorAction D V)
      ((commutatorAction D V).map (MulDistribMulAction.toMulAut K V (c : K)).toMonoidHom) := by
    rw [hmap]
    exact oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE
  have hline : commutatorAction (Subgroup.zpowers a) V ≤ commutatorAction D V := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨mover, vector, rfl⟩
    exact ⟨⟨mover, (Subgroup.zpowers_le.mpr haD) mover.property⟩, vector, rfl⟩
  exact commutatorAction_card_ge_eight_of_swapped_support S (commutatorAction D V)
    a c haS c.property hD.2.2.1 hrank hline hdisjoint

end Stellmacher.SectionOne
