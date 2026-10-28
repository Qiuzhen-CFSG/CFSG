module

public import Theory.Representation.HexacodeAction.AffinePlaneNormalizer
-- The preceding owner proves the literal four-group image is a best offender.
import all Theory.Representation.HexacodeAction.AffinePlaneNormalizer

/-!
# The opposite elementary plane is self-centralizing in the full affine model

The intersection with the translations is the entire fixed space of its
four-group image. The full pointwise kernel of that space is exactly this
offender. An element centralizing the plane therefore differs from a plane
element by a fixed translation, and belongs to the plane itself.
-/

public noncomputable section
open Atlas.Codes Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.Hexacode
local notation "V" => Multiplicative hexacode
local notation "A" => V ⋊[hexAffineAction] HexAutomorphisms
local notation "ι" => (SemidirectProduct.inl : V→*A)
local notation "π" => (SemidirectProduct.rightHom : A→*HexAutomorphisms)

theorem affine_elementary_plane_centralizer
    (W : Subgroup A) [IsElementaryAbelian 2 W]
    (hW : Nat.card W=64) (hI : Nat.card (W⊓(ι).range : Subgroup A)=16) :
    centralizer (W : Set A)=W := by
  have hbest := elementary_plane_image_best W hW hI
  have htrans : Nat.card (W.comap ι)=16 := by
    rw [←card_map_of_injective (K := W.comap ι) (f := ι) SemidirectProduct.inl_injective,
      map_comap_eq,inf_comm]
    exact hI
  have hfix (v : V) (hv : ι v∈centralizer (W : Set A)) :
      v.toAdd∈fixedSpace action (W.map π) := by
    intro d
    obtain ⟨w,hw,hd⟩ := d.property
    have hh := congrArg SemidirectProduct.left (hv w hw)
    change w.left * hexAffineAction w.right v = v * hexAffineAction 1 w.left at hh
    rw [map_one,MulAut.one_apply,mul_comm v w.left] at hh
    have he := congrArg Multiplicative.toAdd (mul_left_cancel hh)
    change action d.val v.toAdd=v.toAdd
    rw [←hd]
    exact he
  have hWC : W≤centralizer (W : Set A) := by
    intro x hx w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hw⟩:W) ⟨x,hx⟩)
  let j : W.comap ι→fixedSpace action (W.map π) := fun v => ⟨v.val.toAdd,hfix v.val (hWC v.property)⟩
  have hj : Function.Injective j := by
    intro v w he
    apply Subtype.ext
    change v.val.toAdd=w.val.toAdd
    exact congrArg (fun x => x.val) he
  have hc : Nat.card (fixedSpace action (W.map π))=16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),bestOffender_fixedSpace_finrank _ hbest,Nat.card_zmod]
    decide
  have hsurj : Function.Surjective j := (hj.bijective_of_nat_card_le (by rw [hc,htrans])).surjective
  have hback (v : V) (hv : v.toAdd∈fixedSpace action (W.map π)) : ι v∈W := by
    obtain ⟨w,he⟩ := hsurj ⟨v.toAdd,hv⟩
    have hw : w.val=v := Multiplicative.toAdd.injective (congrArg (fun x => x.val) he)
    exact hw ▸ w.property
  apply le_antisymm ?_ hWC
  intro x hx
  have hactor : x.right∈W.map π := by
    rw [bestOffender_eq_kernel _ hbest]
    refine ⟨mem_top _,?_⟩
    intro v hv
    have hh := congrArg SemidirectProduct.left (hx (ι (Multiplicative.ofAdd v))
      (hback _ hv))
    change Multiplicative.ofAdd v * hexAffineAction 1 x.left =
      x.left * hexAffineAction x.right (Multiplicative.ofAdd v) at hh
    rw [map_one,MulAut.one_apply,mul_comm (Multiplicative.ofAdd v) x.left] at hh
    exact (congrArg Multiplicative.toAdd (mul_left_cancel hh)).symm
  obtain ⟨w,hw,he⟩ := hactor
  have hy : x*w⁻¹∈(π).ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv]
    change x.right*(w.right)⁻¹=1
    change w.right=x.right at he
    rw [he,mul_inv_cancel]
  rw [←SemidirectProduct.range_inl_eq_ker_rightHom] at hy
  obtain ⟨v,hv⟩ := hy
  have hvC : ι v∈centralizer (W : Set A) := hv.symm ▸
    (centralizer (W : Set A)).mul_mem hx ((centralizer (W : Set A)).inv_mem (hWC hw))
  have hvW := hback v (hfix v hvC)
  have hh := W.mul_mem (hv ▸ hvW) hw
  simpa only [inv_mul_cancel_right] using hh

end Representation.Hexacode
