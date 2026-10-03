module

public import Stellmacher.LaterDefs
public import Stellmacher.SL2DerivedCard
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual

/-!
# Odd residual image in the SL₂(2) quotient

The two-residual of SL₂(2) is its order-three derived subgroup: its
two-group quotient has order dividing six, hence at most two and is abelian.
Conversely, the derived quotient has order two, so residual minimality
gives the opposite containment. Residual functoriality then supplies the
odd-image input for the native equation-(2) centralizer-rigidity adapter.

This does not assert the generated centralizer-rigidity theorem itself.
-/

namespace Stellmacher.SectionEight

open Later

private theorem sl2_residual_normal :
    (twoResidualAmbient (⊤ : Subgroup SL2Two)).Normal := by
  have hres : (twoResidualSubgroup (⊤ : Subgroup SL2Two)).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun subgroup ↦
      Subgroup.normal_iInf_normal fun hsubgroup ↦ hsubgroup.1
  unfold twoResidualAmbient
  exact hres.map _ fun element ↦ ⟨⟨element, by simp⟩, rfl⟩

public theorem eight_six_sl2_residual_eq_commutator :
    twoResidualAmbient (⊤ : Subgroup SL2Two) = commutator SL2Two := by
  let residual := twoResidualAmbient (⊤ : Subgroup SL2Two)
  let _ : residual.Normal := sl2_residual_normal
  have hmodel : IsSL2Two SL2Two := ⟨MulEquiv.refl _⟩
  have hcard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hmodel
  have hderived : Nat.card (commutator SL2Two) = 3 :=
    isSL2Two_commutator_card hmodel
  have hquotient : IsPGroup 2 (SL2Two ⧸ residual) := by
    let _ : (BenderSuzuki.External.hktPResidual 2 SL2Two).Normal :=
      BenderSuzuki.External.hktPResidual_normal
    exact BenderSuzuki.External.hktPResidual_quotient_isPGroup.of_equiv
      (QuotientGroup.quotientMulEquivOfEq
        (SectionThree.twoResidualAmbient_top_eq_hktPResidual (Q := SL2Two))).symm
  have hquotient_dvd : Nat.card (SL2Two ⧸ residual) ∣ 6 := by
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card residual
  have hquotient_le : Nat.card (SL2Two ⧸ residual) ≤ 2 := by
    obtain ⟨exponent, hexponent⟩ := hquotient.exists_card_eq
    have hexponent_le : exponent ≤ 1 := by
      by_contra! hlarge
      have hfour : 4 ∣ 6 := by
        apply dvd_trans (show 2 ^ 2 ∣ 2 ^ exponent from pow_dvd_pow 2 (by omega))
        rwa [← hexponent]
      norm_num at hfour
    rw [hexponent]
    interval_cases exponent <;> norm_num
  have hcommutative : IsMulCommutative (SL2Two ⧸ residual) := by
    have hpositive : 0 < Nat.card (SL2Two ⧸ residual) := Nat.card_pos
    have hcases : Nat.card (SL2Two ⧸ residual) = 1 ∨
        Nat.card (SL2Two ⧸ residual) = 2 := by omega
    apply (isCyclic_of_card_dvd_prime (p := 2) ?_).isMulCommutative
    rcases hcases with hone | htwo <;> simp [*]
  have hderived_le : commutator SL2Two ≤ residual :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommutative
  have hderived_quotient : IsPGroup 2 (SL2Two ⧸ commutator SL2Two) := by
    have hcount := (commutator SL2Two).card_mul_index
    rw [hderived, hcard, Subgroup.index_eq_card] at hcount
    apply IsPGroup.iff_card.mpr
    exact ⟨1, by norm_num; omega⟩
  exact le_antisymm (by
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_le _ inferInstance hderived_quotient)
    hderived_le

public theorem eight_six_odd_residual_image_of_sl2
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (projection : G →* SL2Two)
    (hsurjective : Function.Surjective projection) (_hkernel : projection.ker = Q) :
    Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup G)).map projection)) := by
  rw [map_twoResidualAmbient_of_subgroup_image ⊤ projection ⊤
    (Subgroup.map_top_of_surjective projection hsurjective)]
  have hle : twoResidualAmbient (⊤ : Subgroup SL2Two) ≤ commutator SL2Two :=
    eight_six_sl2_residual_eq_commutator.le
  apply Odd.of_dvd_nat _ (Subgroup.card_dvd_of_le hle)
  rw [isSL2Two_commutator_card (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
  decide

end Stellmacher.SectionEight
