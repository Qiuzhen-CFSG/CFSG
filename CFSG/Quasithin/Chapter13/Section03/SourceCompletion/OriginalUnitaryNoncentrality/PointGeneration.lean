module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicGeneration

/-!
# Generation under the literal point centralizer

The point centralizer in L covers the native derived point parabolic.
The plane cubic generates the derived group under that parabolic. The
natural action kernel lies in the same point centralizer, so two-perfect
lifting gives generation in L itself. This supplies reduction (f) from
the selected component normalizer in (e), without a seed-stabilizer premise.

Source: Aschbacher--Smith 13.3.14(f), printed p.892.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

theorem unitary_plane_residual_point_generation
    (L B Z:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane) (hz:pointCoordinateSubspace E Z=pointLine)
    (hBV:B≤V) (hZV:Z≤V) (hLN:L≤normalizer (V:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2) (hres:pResidual 2 L=⊤)
    (hd:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho) :
    conjugateSpanBy ((pResidual 2 (L⊓normalizer (B:Set G):Subgroup G)).map
      (L⊓normalizer (B:Set G)).subtype) (L⊓centralizer (Z:Set G))=L := by
  let X:Subgroup G:=(pResidual 2 (L⊓normalizer (B:Set G):Subgroup G)).map
    (L⊓normalizer (B:Set G)).subtype
  let P:=L⊓centralizer (Z:Set G)
  have hXL:X≤L:=(map_subtype_le _).trans inf_le_left
  let A:=X.subgroupOf L
  let Q:=P.subgroupOf L
  let f:L→*Atlas.G2.Model F:=rho.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN))
  let : Group.IsPerfect L:=component_isPerfect_of_unitary_action L rho E he hLN hfaith hres hd
  have hf:f.range=commutator (Atlas.G2.Model F) := by
    apply le_antisymm
    · calc
        f.range=(commutator L).map f := by rw [Group.IsPerfect.commutator_eq_top,←MonoidHom.range_eq_map]
        _=⁅f.range,f.range⁆:=map_commutator_eq (f:=f)
        _≤commutator (Atlas.G2.Model F):=commutator_mono le_top le_top
    · intro g hg
      obtain ⟨i,⟨n,hnL,rfl⟩,hnative⟩:=hd hg
      exact ⟨⟨n.val,hnL⟩,hnative⟩
  have hA:zpowers cubicActor≤A.map f := by
    apply zpowers_le.mpr
    obtain ⟨i,⟨n,hnX,rfl⟩,hnative⟩:=source_plane_residual_cubic L B rho E he hp hBV hLN hd
    exact ⟨⟨n.val,hXL hnX⟩,hnX,hnative⟩
  have hQ:derivedSecondAmbient≤Q.map f := by
    intro g hg
    obtain ⟨i,⟨n,hnL,rfl⟩,hnative⟩:=hd hg.2
    have hnZ:n.val∈centralizer (Z:Set G) := by
      intro z hz'
      let v:Additive V:=Additive.ofMul ⟨z,hZV hz'⟩
      have hv:E v∈pointLine:=hz ▸ (mem_pointCoordinateSubspace E Z v).mpr hz'
      have hf:=pointParabolic_fixes_pointLine g hg.1 (E v) hv
      rw [←hnative,←he] at hf
      have hh:n.val*z*n.val⁻¹=z:=congrArg (fun w:Additive V=>(w.toMul:G)) (E.injective hf)
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact ⟨⟨n.val,hnL⟩,⟨hnL,hnZ⟩,hnative⟩
  have hkP:f.ker≤Q := by
    intro n hn
    refine ⟨n.prop,?_⟩
    intro z hz'
    let v:Additive V:=Additive.ofMul ⟨z,hZV hz'⟩
    have hh:=he (V.normalizerMonoidHom.rangeRestrict (inclusion hLN n)) v
    have hfn:f n=1:=hn
    change E (automizerRepresentation V _ v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (f n) (E v) at hh
    rw [hfn,map_one,Module.End.one_apply] at hh
    have hc:n.val*z*n.val⁻¹=z:=congrArg (fun w:Additive V=>w.toMul.val) (E.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hgen:conjugateSpanBy A Q=⊤ := by
    apply conjugateSpanBy_eq_top_of_image 2 f A Q hres
      (component_action_kernel_isTwo L rho E he hLN hfaith) hkP
    apply le_antisymm (map_le_range _ _)
    rw [hf,map_conjugateSpanBy,←Atlas.G2.Natural.BinaryFlagGeneration.cubic_span_ambient]
    exact conjugateSpanBy_mono hA hQ
  have h:=congrArg (fun K:Subgroup L=>K.map L.subtype) hgen
  rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hXL,
    map_subgroupOf_eq_of_le (show P≤L from inf_le_left),
    ←MonoidHom.range_eq_map,L.range_subtype] at h
  exact h
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
