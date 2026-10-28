module

public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import Theory.Representation.SL2CubicFixedSection
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation

/-!
# Cubic fixed spaces on the natural binary SL₂(4) module

A cubic actor fixing a nonzero vector can be conjugated to an upper
triangular matrix. The general characteristic-two Borel calculation then
forces that vector to vanish. Thus every subgroup of order three has zero
invariants and fixed index sixteen on the literal scalar-restricted natural
module.

Source application: Aschbacher–Smith 13.7.13, printed pp.942–943, the
natural SL₂(4) chief-factor branch. The fixed-index conclusion retains the
actual subgroup inclusion and PointCommutator representation.
-/

@[expose] public section
open Matrix Subgroup
namespace Representation.SL2FourNatural
/-- A genuine cubic in SL₂(4) fixes no nonzero natural vector. -/
theorem cubic_fixed_eq_zero (g : SL) (hg : orderOf g = 3)
    (v : V) (hv : action g v = v) : v = 0 := by
  by_contra hn
  obtain ⟨A, hA⟩ := exists_first_column v hn
  let h : SL := (MulAut.conj A⁻¹) g
  have hh : action h (![1, 0] : V) = ![1, 0] := by
    change action (A⁻¹ * g * (A⁻¹)⁻¹) _ = _
    simp only [inv_inv, map_mul, LinearEquiv.mul_apply]
    rw [hA, hv, ← hA]
    simp
  have hB : h ∈ Matrix.SpecialLinearGroup.rankOneBorel F := by
    apply (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mpr
    have ht := congrFun hh 1
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using ht
  have ho : orderOf h = 3 := (MulAut.conj A⁻¹).orderOf_eq g |>.trans hg
  have hz := Representation.SL2CubicFixedSection.cubic_borel_fixed_eq_zero h ho hB
    (![1, 0] : V) hh
  have := congrFun hz 0
  simp at this

/-- An actual order-three subgroup has zero natural invariants. -/
theorem cubic_invariants_eq_bot (A : Subgroup SL) (hA : Nat.card A = 3) :
    Representation.invariants (PointCommutator.representation.comp A.subtype) = ⊥ := by
  have hn : A ≠ ⊥ := by
    intro he
    have ho : Nat.card A = 1 := Subgroup.card_eq_one.mpr he
    omega
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have hp : a.val ^ 3 = 1 := by
    have ht : a ^ 3 = 1 := hA ▸ pow_card_eq_one'
    exact congrArg Subtype.val ht
  have ho : orderOf a.val = 3 := orderOf_eq_prime hp (fun h => hane (Subtype.ext h))
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  exact cubic_fixed_eq_zero a.val ho v (hv a)

/-- The literal natural binary module has fixed index sixteen for an order-three actor. -/
theorem cubic_fixedIndex (A : Subgroup SL) (hA : Nat.card A = 3) :
    BinaryFixedPoints.fixedIndex (PointCommutator.representation.comp A.subtype) = 16 := by
  have h := BinaryFixedPoints.fixedIndex_mul_card
    (PointCommutator.representation.comp A.subtype)
  rw [cubic_invariants_eq_bot A hA] at h
  have hb : Nat.card (⊥ : Submodule (ZMod 2) V) = 1 := Nat.card_unique
  rw [hb, mul_one, Nat.card_eq_fintype_card, card_vector] at h
  exact h

end Representation.SL2FourNatural
