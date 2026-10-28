module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PlaneAction
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
/-!
# Perfection of the original binary unitary component

The literal natural action has a two-group kernel by the source faithful
kernel bound. Two-perfectness kills the binary G₂ sign, so the image is
the actual perfect derived group. Perfection then lifts through that
kernel. Thus the point-kernel argument requires no separate perfection
assumption on the original component.

Source: the unitary case of 13.3.2 applied in 13.3.18, printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- The marked component action has a two-group kernel on the original L. -/
theorem component_action_kernel_isTwo (L:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hLN:L≤normalizer (V:Set G)) (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2) :
    IsPGroup 2 (rho.comp (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN))).ker := by
  let f:=rho.comp (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN))
  have hk:f.ker≤(L.pCoreIn 2).comap L.subtype := by
    intro l hl
    apply hfaith
    refine ⟨l.prop,?_⟩
    intro v hv
    let w:Additive V:=Additive.ofMul ⟨v,hv⟩
    have hh:=he (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w
    have hf:f l=1:=hl
    change E (automizerRepresentation V _ w)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (f l) (E w) at hh
    rw [hf,map_one,Module.End.one_apply] at hh
    have hc:l.val*v*l.val⁻¹=v:=congrArg (fun x:Additive V=>(x.toMul:G)) (E.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  exact ((isPGroup_pCoreIn 2 L).comap_subtype).to_le hk

/-- Two-perfectness, the actual natural derived image and its two-group
kernel imply perfection of the original component. -/
theorem component_isPerfect_of_unitary_action (L:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hLN:L≤normalizer (V:Set G)) (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (hres:pResidual 2 L=⊤)
    (hderived:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho) :
    Group.IsPerfect L := by
  let f:L→*Atlas.G2.Model F:=rho.comp (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN))
  have hperfect:IsPPerfect 2 L:=(pResidual_eq_top_iff 2 L).mp hres
  have hu:IsPGroup 2 ℤˣ:=IsPGroup.of_card (n:=1) (by
    simp [Nat.card_eq_fintype_card,Fintype.card_units_int])
  have hsign:=hperfect.hom_eq_one_of_isPGroup hu (Atlas.G2.Binary.lineSign.comp f)
  have him:∀l:L,f l∈commutator (Atlas.G2.Model F) := by
    intro l
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      ←Atlas.G2.BinaryException.lineSign_kernel]
    exact DFunLike.congr_fun hsign l
  let q:=f.codRestrict (commutator (Atlas.G2.Model F)) him
  have hq:Function.Surjective q := by
    intro g
    obtain ⟨i,⟨n,hnL,rfl⟩,heq⟩:=hderived g.prop
    exact ⟨⟨n.val,hnL⟩,Subtype.ext heq⟩
  have hk:IsPGroup 2 q.ker := by
    have heq:q.ker=f.ker:=by ext l;exact Subtype.ext_iff
    rw [heq]
    exact component_action_kernel_isTwo L rho E he hLN hfaith
  let : Group.IsPerfect (commutator (Atlas.G2.Model F)):=by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  exact hperfect.isPerfect_of_surjective_pGroup_kernel q hq hk
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
