module
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# A large two-group has no fixed points in a canonical support

In a faithful Section One action on an elementary group of order sixteen,
a two-subgroup of order greater than four fixes no nonidentity point in any
supplied canonical four-element support. The actual group, module, and
canonical factor remain unchanged.

The support-mover theorem supplies an element of the two-group carrying the
support to a distinct canonical support. These supports are disjoint. A fixed
point in the original support also lies in its moved support, hence is identity.
This is the local wreath obstruction underlying the commutativity step after
Stellmacher (9.10)(**), Journal of Algebra 190 (1997), printed p.58.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_large_two_group_support_fixed_eq_bot
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (D S : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (hS : IsPGroup 2 S)
    (hV : Nat.card V = 16) (hlarge : 4 < Nat.card S) :
    commutatorAction D V ⊓ FixedPoints.subgroup S V = ⊥ := by
  obtain ⟨actor,hmove,_⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D S hD hS hV hlarge
  let E := D.conjBy (actor:K)
  have hmap : (commutatorAction D V).map
      (MulDistribMulAction.toMulAut K V (actor:K)).toMonoidHom = commutatorAction E V :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D (actor:K)
  have hne : D ≠ E := by
    intro heq
    apply hmove
    rw [hmap,←heq]
  have hdisj := oneSevenFactor_support_disjoint_of_ne hyp D E hD
    (hD.conjBy D (actor:K)) hne
  apply le_bot_iff.mp
  intro point hpoint
  have hfixed : (actor:K) • point = point := hpoint.2 actor
  have hother : point ∈ commutatorAction E V := by
    rw [←hmap]
    exact ⟨point,hpoint.1,hfixed⟩
  exact hdisj.le_bot ⟨hpoint.1,hother⟩

end Stellmacher.SectionOne
