module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.SylowAffineModel
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.SylowAffine

/-!
# Original-plane square containment in arbitrary even affine Sylows

The marked Sylow equivalence carries both W and its intersection with the
normal translations to the standard model. The native square calculation
therefore applies to the same W in every actual Sylow of the even affine group.
-/

public noncomputable section
open Subgroup Atlas.Codes Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
local notation "V" => Multiplicative hexacode
local notation "A" => V ⋊[hexAffineAction.comp hexSign.ker.subtype] HexEvenAutomorphisms
local notation "P" => V ⋊[MonoidHom.comp (MonoidHom.comp hexAffineAction hexSign.ker.subtype) sylowGroup.subtype] sylowGroup

public theorem affine_sylow_squares_mem
    (S : Sylow 2 A) (W : Subgroup A) [IsElementaryAbelian 2 W]
    (hWS : W≤(S : Subgroup A)) (hSW : (S : Subgroup A)≤normalizer (W : Set A))
    (hW : Nat.card W=64)
    (hI : Nat.card (W⊓(SemidirectProduct.inl : V→*A).range : Subgroup A)=16) :
    ∀x∈(S : Subgroup A), x^2∈W := by
  obtain ⟨e,he⟩ := exists_marked_affine_sylow_equiv S
  let W₀ := (W.subgroupOf S).map e.toMonoidHom
  let : (W.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hSW
  let : W₀.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 (W.subgroupOf S) := IsElementaryAbelian.subgroupOf hWS
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map _
  have hW₀ : Nat.card W₀=64 := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv]
    exact hW
  have hi : W₀⊓(SemidirectProduct.inl : V→*P).range=
      ((W⊓(SemidirectProduct.inl : V→*A).range).subgroupOf S).map e.toMonoidHom := by
    change (W.subgroupOf S).map e.toMonoidHom⊓(SemidirectProduct.inl : V→*P).range=_
    rw [←he,←Subgroup.map_inf _ _ _ e.injective]
    rfl
  have hI₀ : Nat.card (W₀⊓(SemidirectProduct.inl : V→*P).range : Subgroup P)=16 := by
    rw [hi,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hWS)).toEquiv]
    exact hI
  intro x hx
  have hh := affine_squares_mem W₀ hW₀ hI₀ (e ⟨x,hx⟩)
  have hmem : (⟨x,hx⟩:S)^2∈W.subgroupOf S := by
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    change e ((⟨x,hx⟩:S)^2)∈W₀
    rwa [map_pow]
  exact hmem

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
