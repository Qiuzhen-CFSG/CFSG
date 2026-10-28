module

public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The intrinsic plane join in the full hexacode affine group

An elementary subgroup of order 64 with translation intersection of order 16
has an offending four-group image. Uniqueness of the hexacode best offender
inside a two-group makes the join with the translations invariant under every
containing two-group. This retains the actual elementary subgroup and the
whole translation kernel.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.Hexacode
local notation "V" => Multiplicative hexacode
local notation "A" => V ⋊[hexAffineAction] HexAutomorphisms
local notation "ι" => (SemidirectProduct.inl : V→*A)
local notation "π" => (SemidirectProduct.rightHom : A→*HexAutomorphisms)

private theorem elementary_plane_image_best
    (W : Subgroup A) [IsElementaryAbelian 2 W]
    (hW : Nat.card W=64) (hI : Nat.card (W⊓(ι).range : Subgroup A)=16) :
    IsBestOffender action (W.map π) := by
  have hc : Nat.card (W.map π)=4 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map W π
    rw [←SemidirectProduct.range_inl_eq_ker_rightHom,hI,hW] at hh
    omega
  have htrans : Nat.card (W.comap ι)=16 := by
    rw [←card_map_of_injective (K := W.comap ι) (f := ι) SemidirectProduct.inl_injective,
      map_comap_eq,inf_comm]
    exact hI
  let j : W.comap ι → fixedSpace action (W.map π) := fun v => ⟨v.val.toAdd,by
    intro d
    obtain ⟨w,hw,hd⟩ := d.property
    have hh := congrArg (fun x : W => x.val.left)
      (mul_comm (⟨w,hw⟩ : W) ⟨ι v.val,v.property⟩)
    change w.left * hexAffineAction w.right v.val = v.val * hexAffineAction 1 w.left at hh
    rw [map_one,MulAut.one_apply,mul_comm v.val w.left] at hh
    have he := congrArg Multiplicative.toAdd (mul_left_cancel hh)
    change action d.val v.val.toAdd=v.val.toAdd
    rw [←hd]
    exact he⟩
  have hj : Function.Injective j := by
    intro v w hvw
    apply Subtype.ext
    change v.val.toAdd=w.val.toAdd
    exact congrArg (fun x => x.val) hvw
  have hdim : 4≤Module.finrank (ZMod 2) (fixedSpace action (W.map π)) := by
    have hh := Nat.card_le_card_of_injective j hj
    rw [htrans,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hh
  have ho : IsOffender action (W.map π) := by
    refine ⟨⟨?_,IsElementaryAbelian.map _⟩,?_⟩
    · intro he; rw [he,card_bot] at hc; omega
    · have hh := fixedCodim_add_finrank action (W.map π)
      rw [hexacode_finrank] at hh
      rw [rank,hc]
      change fixedCodim action (W.map π)≤2
      omega
  obtain ⟨B,hB,hbest⟩ := ho.exists_bestOffender action
  have he : B=W.map π := eq_of_le_of_card_ge hB (by rw [bestOffender_card B hbest,hc])
  exact he ▸ hbest

/-- The actual plane join is normalized by every containing two-subgroup of
the full affine group. No normalization of the second plane is assumed. -/
theorem affine_normalizes_plane_join
    (S W : Subgroup A) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 W] (hWS : W≤S)
    (hW : Nat.card W=64) (hI : Nat.card (W⊓(ι).range : Subgroup A)=16) :
    S≤normalizer (((ι).range⊔W : Subgroup A) : Set A) := by
  have hbest := elementary_plane_image_best W hW hI
  have hnorm : S.map π≤normalizer (W.map π : Set HexAutomorphisms) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply bestOffender_unique_in_pgroup (S.map π) (hS.map π)
    · exact (map_mono (f := (MulAut.conj x).toMonoidHom) (map_mono hWS)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp ((S.map π).le_normalizer hx))
    · exact map_mono hWS
    · exact hbest.map_conj action x
    · exact hbest
  have hpre : (W.map π).comap π=(ι).range⊔W := by
    rw [comap_map_eq,←SemidirectProduct.range_inl_eq_ker_rightHom,sup_comm]
  rw [←hpre]
  exact (map_le_iff_le_comap.mp hnorm).trans (le_normalizer_comap π)

end Representation.Hexacode
