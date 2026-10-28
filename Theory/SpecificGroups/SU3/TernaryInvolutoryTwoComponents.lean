module

public import Theory.SpecificGroups.SU3.TernaryInvolutionCentralizer
public import Theory.SpecificGroups.SU3.OddInvolutionFixed
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.OrthogonalOrder
public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.FieldTheory.QuadraticFrobeniusFixed

/-!
# The B₂ condition for PSU₃(3)

Inner involutions have solvable centralizers by the explicit GU₂(3)
calculation. Every outer involution has the full SO₃(3) fixed group, whose
order divides 24; its Sylow two-subgroup has index at most three, so this
fixed group is solvable too. Thus no involution fixed group has a two-component.

The automorphisms act on the actual projective unitary matrix image. Simplicity
is the inherited source hypothesis, and no Sylow-fixation assumption is used.
Sources: GLS II Definition 2.4; GLS III §§2.7 and 4.3; the matrix calculations
and their source references are in the imported SU₃ modules.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups

private theorem solvable_of_card_dvd_twenty_four {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ∣ 24) : Group.IsSolvable G := by
  let P : Sylow 2 G := Classical.choice inferInstance
  have hcop : Nat.Coprime (P : Subgroup G).index (2 ^ 3) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index).symm.pow_right 3
  have hi : (P : Subgroup G).index ∣ 3 :=
    hcop.dvd_of_dvd_mul_left ((P : Subgroup G).index_dvd_card.trans hc)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact (P : Subgroup G).isSolvable_of_index_le_four
    ((Nat.le_of_dvd (by decide : 0 < 3) hi).trans (by decide))

private theorem inner_order {G : Type*} [Group G] [IsSimpleGroup G]
    (k : G) (hk : orderOf (MulAut.conj k) = 2) : orderOf k = 2 := by
  have hc : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hmem : k ∈ center G := by rw [hc]; trivial
      have hone : MulAut.conj k = 1 := by
        ext x
        change k * x * k⁻¹ = x
        rw [← mem_center_iff.mp hmem x, mul_inv_cancel_right]
      simp only [hone, orderOf_one] at hk
      omega
  exact (MulAut.conj_orderOf_of_center_eq_bot hc k).symm.trans hk

namespace Matrix.SU3

theorem ternary_fixed_solvable [IsSimpleGroup (ABG.PSU3 3 1 one_ne_zero)]
    (a : MulAut (ABG.PSU3 3 1 one_ne_zero)) (ha : orderOf a = 2) :
    Group.IsSolvable a.fixedSubgroup := by
  by_cases hi : ∃ k, a = MulAut.conj k
  · obtain ⟨k, rfl⟩ := hi
    rw [MulAut.fixedSubgroup_conj]
    exact TernaryCentralizer.standard_involution_centralizer_solvable k (inner_order k ha)
  · let J := ABG.unitaryForm 3 3 1 one_ne_zero
    have hcard : Nat.card (GaloisField 3 (2 * 1)) = 3 ^ 2 :=
      GaloisField.card 3 (2 * 1) (by decide)
    have hfixed : Nat.card {x : GaloisField 3 (2 * 1) // J.conj x = x} = 3 := by
      exact GaloisField.card_fixedBy_quadraticFrobenius 3 1 one_ne_zero
    obtain ⟨e⟩ := HermitianForm.OddInvolutionNormalization.fixed_equiv_orthogonal
      J Nat.prime_three (by decide) hcard hfixed a
      (by simpa only [ha] using pow_orderOf_eq_one a) hi
    let : Finite a.fixedSubgroup := Finite.of_equiv _ e.toEquiv.symm
    have hc : Nat.card a.fixedSubgroup ∣ 24 := by
      rw [Nat.card_congr e.toEquiv]
      exact HermitianForm.OddPrimeSylow.card_splitOrthogonal_specialSubgroup_dvd
        (by decide : 3 % 8 = 3) hfixed
    exact solvable_of_card_dvd_twenty_four hc

theorem ternary_hasInvolutoryB2 [IsSimpleGroup (ABG.PSU3 3 1 one_ne_zero)] :
    Theory.GroupTheory.HasInvolutoryB2 (ABG.PSU3 3 1 one_ne_zero) :=
  Theory.GroupTheory.HasInvolutoryB2.of_fixed_solvable ternary_fixed_solvable

end Matrix.SU3
