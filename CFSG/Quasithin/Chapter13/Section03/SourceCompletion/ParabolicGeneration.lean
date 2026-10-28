module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ComponentPerfect
public import Theory.Representation.G2BinaryFlagGeneration
public import Theory.GroupTheory.ConjugateSpanResidualLift
/-!
# Generation by the original unitary plane residual

The actual plane residual contains the native cubic in its action image.
The original normalizer of the marked three-space covers the derived point
parabolic. Native conjugate generation therefore fills the original action
image. Its two-group kernel lies in that same three-space normalizer, so
two-perfectness lifts the generation identity to the original component.

Source: Aschbacher–Smith 13.3.15(6), printed p.894.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.BinaryParabolicPair
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

theorem unitary_plane_residual_generation
    (L B R:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane) (hs:pointCoordinateSubspace E R=seed)
    (hBV:B≤V) (hRV:R≤V) (hLN:L≤normalizer (V:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2) (hres:pResidual 2 L=⊤)
    (hd:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho) :
    conjugateSpanBy ((pResidual 2 (L⊓normalizer (B:Set G):Subgroup G)).map
      (L⊓normalizer (B:Set G)).subtype) (L⊓normalizer (R:Set G))=L := by
  let X:Subgroup G:=(pResidual 2 (L⊓normalizer (B:Set G):Subgroup G)).map
    (L⊓normalizer (B:Set G)).subtype
  let P:=L⊓normalizer (R:Set G)
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
    have hnR:n.val∈normalizer (R:Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hmap:R.map (MulAut.conj n.val).toMonoidHom≤R := by
        rintro _ ⟨r,hr,rfl⟩
        let v:Additive V:=Additive.ofMul ⟨r,hRV hr⟩
        have hv:E v∈seed:=hs ▸ (mem_pointCoordinateSubspace E R v).mpr hr
        have hh:=pointParabolic_preserves_seed g hg.1 (E v) hv
        rw [←hnative,←he,←hs,mem_pointCoordinateSubspace] at hh
        exact hh
      apply eq_of_le_of_card_ge hmap
      rw [card_map_of_injective (MulAut.conj n.val).injective]
    exact ⟨⟨n.val,hnL⟩,⟨hnL,hnR⟩,hnative⟩
  have hkP:f.ker≤Q := by
    intro n hn
    refine ⟨n.prop,?_⟩
    apply Subgroup.centralizer_le_normalizer
    intro r hr
    let v:Additive V:=Additive.ofMul ⟨r,hRV hr⟩
    have hh:=he (V.normalizerMonoidHom.rangeRestrict (inclusion hLN n)) v
    have hfn:f n=1:=hn
    change E (automizerRepresentation V _ v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (f n) (E v) at hh
    rw [hfn,map_one,Module.End.one_apply] at hh
    have hc:n.val*r*n.val⁻¹=r:=congrArg (fun w:Additive V=>w.toMul.val) (E.injective hh)
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
