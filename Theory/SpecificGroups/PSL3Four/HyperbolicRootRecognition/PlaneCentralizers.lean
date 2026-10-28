module
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.PlaneNormality

/-!
# Centralizers of the actual root planes

An element centralizing a noncentral point of a root plane has zero opposite
root coordinate. Thus every subgroup of a plane with order greater than four
has the whole plane as its centralizer. The proof transports through arbitrary
literal root equivalences and supplies the source normalizer kernel calculation.
Source: Aschbacher, Sporadic Groups (1994), 45.6, printed p.244.
-/

public section
open Subgroup Matrix.PSL3Four
namespace Theory.GroupTheory.HyperbolicRecognition

theorem rootPlane₁_centralizer : Subgroup.centralizer (rootPlane₁:Set RootNormalizerModel.Root)=rootPlane₁ := by
  apply le_antisymm
  · intro x hx
    apply (mem_rootPlane₁ x).mpr
    have hm : (⟨1,0,0⟩:RootNormalizerModel.Root)∈rootPlane₁ := by simp
    have hh := (SylowModel.commute_iff _ _).mp (hx _ hm)
    simpa using hh
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem rootPlane₂_centralizer : Subgroup.centralizer (rootPlane₂:Set RootNormalizerModel.Root)=rootPlane₂ := by
  apply le_antisymm
  · intro x hx
    apply (mem_rootPlane₂ x).mpr
    have hm : (⟨0,1,0⟩:RootNormalizerModel.Root)∈rootPlane₂ := by simp
    have hh := (SylowModel.commute_iff _ _).mp (hx _ hm)
    simpa using hh.symm
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem elementary_sixteen_centralizer (V:Subgroup RootNormalizerModel.Root)
    [IsElementaryAbelian 2 V] (hV:Nat.card V=16) : Subgroup.centralizer (V:Set RootNormalizerModel.Root)=V := by
  rcases (elementary_sixteen_iff V).mp ⟨inferInstance,hV⟩ with rfl | rfl
  · exact rootPlane₁_centralizer
  · exact rootPlane₂_centralizer

theorem transported_sixteen_centralizer {K:Type*} [Group K]
    (e:K≃*RootNormalizerModel.Root) (V:Subgroup K) [IsElementaryAbelian 2 V] (hV:Nat.card V=16) :
    Subgroup.centralizer (V:Set K)=V := by
  let W := V.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hW : Nat.card W=16 := (card_map_of_injective e.injective).trans hV
  apply le_antisymm
  · intro x hx
    have he : e x∈Subgroup.centralizer (W:Set RootNormalizerModel.Root) := by
      rintro y ⟨v,hv,rfl⟩
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e (hx v hv)
    rw [elementary_sixteen_centralizer W hW] at he
    obtain ⟨v,hv,he⟩:=he
    exact e.injective he ▸ hv
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

theorem root_big_plane_centralizer (V U:Subgroup RootNormalizerModel.Root)
    [IsElementaryAbelian 2 V] (hV:Nat.card V=16) (hUV:U≤V)
    (hU:4<Nat.card U) : Subgroup.centralizer (U:Set RootNormalizerModel.Root)=V := by
  have hnot : ¬ U≤center RootNormalizerModel.Root := by
    intro hu
    have hc:=card_le_of_le hu
    have hcenter : Nat.card (center RootNormalizerModel.Root)=4 := by
      rw [←rootPlanes_inf]
      exact Nat.card_congr (show (rootPlane₁⊓rootPlane₂:Subgroup RootNormalizerModel.Root)≃F from
        { toFun := fun x=>x.val.c
          invFun := fun c=>⟨⟨0,0,c⟩,by simp⟩
          left_inv := fun x=>Subtype.ext (SylowModel.U.ext
            ((mem_rootPlane₂ x).mp x.property.2).symm
            ((mem_rootPlane₁ x).mp x.property.1).symm rfl)
          right_inv := fun _=>rfl }) |>.trans card_F
    omega
  obtain ⟨u,hu,huz⟩:=SetLike.not_le_iff_exists.mp hnot
  have hc : V≤Subgroup.centralizer (U:Set RootNormalizerModel.Root) :=
    le_centralizer_iff.mpr (hUV.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  apply le_antisymm _ hc
  rcases (elementary_sixteen_iff V).mp ⟨inferInstance,hV⟩ with rfl | rfl
  · have huy : u.y=0 := (mem_rootPlane₁ u).mp (hUV hu)
    have hux : u.x≠0 := by intro he; exact huz (by simp [SylowModel.mem_center_U,he,huy])
    intro x hx
    apply (mem_rootPlane₁ x).mpr
    have he := (SylowModel.commute_iff _ _).mp (hx u hu)
    rw [huy,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hux
  · have hux : u.x=0 := (mem_rootPlane₂ u).mp (hUV hu)
    have huy : u.y≠0 := by intro he; exact huz (by simp [SylowModel.mem_center_U,he,hux])
    intro x hx
    apply (mem_rootPlane₂ x).mpr
    have he := (SylowModel.commute_iff _ _).mp (hx u hu)
    rw [hux,zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_right huy

theorem transported_big_plane_centralizer {K:Type*} [Group K]
    (e:K≃*RootNormalizerModel.Root) (V U:Subgroup K) [IsElementaryAbelian 2 V]
    (hV:Nat.card V=16) (hUV:U≤V) (hU:4<Nat.card U) :
    Subgroup.centralizer (U:Set K)=V := by
  let W := V.map e.toMonoidHom
  let D := U.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hW : Nat.card W=16 := (card_map_of_injective e.injective).trans hV
  have hD : 4<Nat.card D := by rwa [card_map_of_injective e.injective]
  apply le_antisymm
  · intro x hx
    have he : e x∈Subgroup.centralizer (D:Set RootNormalizerModel.Root) := by
      rintro y ⟨v,hv,rfl⟩
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e (hx v hv)
    rw [root_big_plane_centralizer W D hW (map_mono hUV) hD] at he
    obtain ⟨v,hv,he⟩:=he
    exact e.injective he ▸ hv
  · intro x hx u hu
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=V)).comm ⟨u,hUV hu⟩ ⟨x,hx⟩)
end Theory.GroupTheory.HyperbolicRecognition
