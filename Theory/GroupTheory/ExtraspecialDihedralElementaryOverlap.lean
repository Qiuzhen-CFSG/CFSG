module

public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Elementary64 overlap with an extraspecial128 dihedral kernel

The image of an elementary subgroup of order64 in D8 has order at most4.
Its intersection with an extraspecial kernel of order128 has order at most16
by the central pairing. Both bounds are therefore equalities. The literal
intersection contains the kernel center and is self-centralizing there.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

public theorem extraspecial_dihedral_elementary_overlap
    {S : Type*} [Group S] [Finite S] (π : S→*DihedralGroup 4)
    [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128)
    (U : Subgroup S) [IsElementaryAbelian 2 U] (hU : Nat.card U=64) :
    Nat.card (U⊓π.ker : Subgroup S)=16 ∧ Nat.card (U.map π)=4 ∧
      (center π.ker).map π.ker.subtype≤U ∧
      centralizer (U.subgroupOf π.ker : Set π.ker)=U.subgroupOf π.ker := by
  let A := U.subgroupOf π.ker
  let : IsElementaryAbelian 2 (U⊓π.ker : Subgroup S) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 A := by
    rw [show A=(U⊓π.ker).subgroupOf π.ker from (inf_subgroupOf_right U π.ker).symm]
    exact IsElementaryAbelian.subgroupOf inf_le_right
  have hAc : Nat.card A=Nat.card (U⊓π.ker : Subgroup S) := by
    rw [show A=(U⊓π.ker).subgroupOf π.ker from (inf_subgroupOf_right U π.ker).symm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  let : IsElementaryAbelian 2 (center π.ker) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z => by
      simpa only [IsExtraspecial.center_order_p 2 π.ker] using pow_card_eq_one' (x:=z)) }
  let J := A⊔center π.ker
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.sup_of_le_centralizer
    (center_le_centralizer _)
  have hJ := extraspecial_two_abelian_card_sq_le J le_sup_right
  rw [hP] at hJ
  have hAJ := card_le_of_le (show A≤J from le_sup_left)
  have hAb : Nat.card A≤16 := by nlinarith
  let : IsElementaryAbelian 2 (U.map π) := IsElementaryAbelian.map π
  have hIb : Nat.card (U.map π)≤4 :=
    DihedralGroup.card_le_four_of_square_eq_one _
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (U.map π)))
  have hmul := IsElementaryAbelian.card_inf_ker_mul_card_map U π
  rw [hU,←hAc] at hmul
  have hA : Nat.card A=16 := by nlinarith
  have hI : Nat.card (U.map π)=4 := by nlinarith
  have hAJ' : A=J := eq_of_le_of_card_ge le_sup_left (by rw [hA]; nlinarith)
  have hZA : center π.ker≤A := hAJ'.symm ▸ le_sup_right
  refine ⟨hAc.symm.trans hA,hI,?_,?_⟩
  · rintro x ⟨z,hz,rfl⟩
    exact hZA hz
  · exact extraspecial_two_centralizer_eq_of_card_sq A hZA (by rw [hA,hP]; norm_num)

end Theory.GroupTheory
