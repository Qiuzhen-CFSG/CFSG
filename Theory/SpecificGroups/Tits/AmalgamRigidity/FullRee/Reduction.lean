module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Setup

/-!
# An index-two restriction criterion for the full binary Ree amalgam

It suffices that the first endpoint restriction group have index at most two
and that some automorphism extend to the second endpoint but not the first.
The first group then has index exactly two. Multiplying any automorphism
outside it by the specified second restriction puts it inside, giving the
product in the precise order required by `FactorsThrough`.

The marked coordinate isomorphism transports this product to the actual full
Ree amalgam. The last theorem applies the generic faithful-twist reduction to
arbitrary faithful Sylow-embedded inputs. Bounds of 32768 on the full Sylow
automorphism group and 16384 from below on first restrictions suffice for the
index premise. These bounds and the second restriction remain explicit inputs;
this module does not yet prove the requested Tits-to-full-Ree transfer.

Source context: Aschbacher--Smith F.1.11--12, printed pp.262--263, and Fan,
*Amalgams of prime index*, J. Algebra 98 (1986), pp.375--421. This elementary
criterion does not invoke an unverified formulation of Fan's theorem.
-/

public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee
open Theory.GroupTheory RankTwoAmalgam

/-- The two asymmetric order estimates give the sufficient index bound. -/
theorem firstRestrictions_index_le_two_of_bounds
    (haut : Nat.card (MulAut ReeTwo.SylowModel) ≤ 32768)
    (hfirst : 16384 ≤ Nat.card firstRestrictions) :
    firstRestrictions.index ≤ 2 := by
  have hc := firstRestrictions.card_mul_index
  have hm := Nat.mul_le_mul_right firstRestrictions.index hfirst
  nlinarith

/-- An index-two first restriction group and one second restriction outside it
remove every coordinate twist, without any faithfulness assumption. -/
theorem coordinate_factorsThrough_of_restriction_index
    (hindex : firstRestrictions.index ≤ 2)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions)
    (d : MulAut ReeTwo.SylowModel) : FactorsThrough coordinateAmalgam d := by
  obtain ⟨r, hr, hn⟩ := hsecond
  have hi : firstRestrictions.index = 2 := by
    have hp := firstRestrictions.index_ne_zero_of_finite
    have hne : firstRestrictions.index ≠ 1 := by
      intro h
      exact hn ((Subgroup.index_eq_one.mp h).symm ▸ Subgroup.mem_top r)
    omega
  by_cases hd : d ∈ firstRestrictions
  · refine ⟨d, 1, hd, secondRestrictions.one_mem, ?_⟩
    apply MulEquiv.ext
    intro x
    rfl
  · have hl : r * d ∈ firstRestrictions :=
      (firstRestrictions.mul_mem_iff_of_index_two hi).mpr (iff_of_false hn hd)
    refine ⟨r * d, r, hl, hr, ?_⟩
    apply MulEquiv.ext
    intro x
    exact (r.symm_apply_apply (d x)).symm

/-- Transport the restriction product through both actual inclusion squares. -/
theorem factorsThrough_of_restriction_index
    (hindex : firstRestrictions.index ≤ 2)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions)
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d := by
  obtain ⟨e, rfl⟩ := (MulAut.congr borelEquiv).surjective d
  exact (coordinateAmalgamIso.factorsThrough_iff e).mp
    (coordinate_factorsThrough_of_restriction_index hindex hsecond e)

/-- The three separate concrete calculations suffice for every full Ree twist. -/
theorem factorsThrough_of_bounds
    (haut : Nat.card (MulAut ReeTwo.SylowModel) ≤ 32768)
    (hfirst : 16384 ≤ Nat.card firstRestrictions)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions)
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_restriction_index
    (firstRestrictions_index_le_two_of_bounds haut hfirst) hsecond d

/-- Application to arbitrary faithful Sylow inputs, with the three concrete
calculation premises retained until their independent proofs are supplied. -/
theorem iso_of_bounds
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α ExceptionalParabolics.FullRee.amalgam)
    (haut : Nat.card (MulAut ReeTwo.SylowModel) ≤ 32768)
    (hfirst : 16384 ≤ Nat.card firstRestrictions)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions) :
    Nonempty (Iso α ExceptionalParabolics.FullRee.amalgam) :=
  iso_of_faithful_twist_factorization hα sylowEmbedded hf e
    (fun d _ => factorsThrough_of_bounds haut hfirst hsecond d)

end Tits.AmalgamRigidity.FullRee
