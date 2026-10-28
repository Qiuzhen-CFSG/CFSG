module
public import Stellmacher.SectionOne.LemmaOneThree
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# The canonical odd commutator of a rank-one involution

Under the Section One faithful solvable-action hypotheses, an involution
with displacement of order two has canonical odd commutator F cyclic of
order three whenever F is a p-group. The involution rank-nullity formula
gives fixed-point index two. In the proved classification (1.3), both the
small and extraspecial constructors require fixed-point index four, so
the cyclic-three constructor is the only possible one.

This direct consequence of Stellmacher (1.3), printed pp.15–16, supplies
the rank-one obstruction in (10.1)(15), printed p.63. The latter application
first proves that the actual noncentral chief action preserves the
terminal odd residual image of order five or nine; no such preservation
is assumed or asserted by this action-theoretic lemma.
-/

namespace Stellmacher.SectionOne
universe u

public theorem involutionCommutator_isCyclicThree_of_displacement_card_two
    {K W : Type u} [Group K] [Finite K] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction K W]
    (hyp : Hypotheses K W) (x : K) (hx : _root_.IsInvolution x)
    (p : ℕ) [Fact p.Prime] (hF : IsPGroup p (involutionCommutator K x))
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers x) W)=2) :
    Nonempty (involutionCommutator K x ≃* Multiplicative (ZMod 3)) := by
  let R := Subgroup.zpowers x
  have hRcard : Nat.card R=2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hx.2 hx.1]
  let generator : R := ⟨x,Subgroup.mem_zpowers x⟩
  have hgenerator : generator≠1 ∧ generator^2=1 :=
    ⟨fun hh => hx.1 (congrArg Subtype.val hh),Subtype.ext hx.2⟩
  let _ : Nontrivial W := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    have hh := Subgroup.card_le_card_group (commutatorAction R W)
    rw [hrank] at hh
    omega
  have hfixed := (card_two_action_fixed_commutator_card_data (U:=W)
    generator hgenerator hRcard).1
  change Nat.card W=Nat.card (FixedPoints.subgroup R W)*Nat.card (commutatorAction R W) at hfixed
  rw [hrank] at hfixed
  have hbound : Nat.card W ≤ 4*Nat.card (FixedPoints.subgroup R W) := by omega
  have hpositive : 0 < Nat.card (FixedPoints.subgroup R W) := Nat.card_pos
  have hclass := lemma_one_three hyp x hx p hF hbound
  cases hclass with
  | cyclicThree _ hmodel => exact hmodel
  | small _ hfour _ => change Nat.card W=4*Nat.card (FixedPoints.subgroup R W) at hfour; omega
  | extraspecial _ hfour _ _ _ => change Nat.card W=4*Nat.card (FixedPoints.subgroup R W) at hfour; omega

end Stellmacher.SectionOne
