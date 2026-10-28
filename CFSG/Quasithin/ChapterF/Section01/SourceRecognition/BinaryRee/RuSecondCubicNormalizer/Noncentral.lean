module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Order

/-!
# The source image does not centralize the cubic

Frattini's supplement carries the normalizer onto F₂/A. If its faithful
native image centralized the selected cubic, the nontrivial order-three
image would be central in S₃. Its trivial center contradicts the order of
A. Thus the central alternative of the native normalizer census is absent.

Source: Aschbacher–Smith J.4.4–5/F.1.12, on the original quotient map.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
open Centralizers.Choices ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}
    {B5:Sylow 5 d.toTypeRuSetup.H} (m:SecondCubicMarking (p:=p) B5)
    (s:SourceChoice p) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
include s hi

 theorem image_not_le_centralizer : ¬(secondCubicNormalizerAction B5 m.X m.coordinates).range≤
    centralizer ({CubicAction.cubic}:Set (MulAut firstParabolicCore)) := by
  intro h
  let F:=p.F₂ B5 m.X
  let N:=secondCubicNormalizer B5 m.X
  let A:Subgroup F:=(p.A B5).subgroupOf F
  let φ:=secondCubicNormalizerAction B5 m.X m.coordinates
  obtain ⟨e⟩:=m.quotient
  let q:F→*Equiv.Perm (Fin 3):=e.toMonoidHom.comp (QuotientGroup.mk' A)
  have hq:Function.Surjective q:=e.surjective.comp (QuotientGroup.mk'_surjective A)
  let xF:F:=⟨((m.generator:p.parabolic):G),m.generator_mem.1⟩
  let xN:N:=⟨((m.generator:p.parabolic):G),m.generator_mem⟩
  let D:Subgroup F:=(centralizer ({q xF}:Set (Equiv.Perm (Fin 3)))).comap q
  have hAD:A≤D:=by
    intro a ha
    have ha':q a=1:=by
      change e (a:F⧸A)=1
      rw [(QuotientGroup.eq_one_iff a).mpr ha,e.map_one]
    change q a∈centralizer ({q xF}:Set (Equiv.Perm (Fin 3)))
    rw [ha']
    exact one_mem _
  have hND:N.subgroupOf F≤D:=by
    intro z hz
    let zN:N:=⟨z,hz⟩
    have hc:Commute (φ zN) (φ xN):=by
      rw [show φ xN=CubicAction.cubic from m.action_generator_normalizer]
      exact mem_centralizer_singleton_iff.mp (h ⟨zN,rfl⟩)
    have hcN:Commute zN xN:=(commute_map_iff m.action_injective).mp hc
    have hcF:Commute z xF:=by
      apply Subtype.ext
      exact congrArg (fun a:N=>(a:G)) hcN.eq
    exact mem_centralizer_singleton_iff.mpr (hcF.map q).eq
  have hs:A⊔N.subgroupOf F=⊤:=by
    rw [←subgroupOf_sup (p.A_le_F₂ B5 m.X) (show N≤F from inf_le_left),m.supplement s hi]
    exact subgroupOf_self _
  have hD:D=⊤:=top_unique (hs ▸ sup_le hAD hND)
  have hc:∀y:Equiv.Perm (Fin 3),y*q xF=q xF*y:=by
    intro y
    obtain ⟨z,rfl⟩:=hq y
    have hz:z∈D:=hD.symm ▸ mem_top z
    exact mem_centralizer_singleton_iff.mp hz
  have hcenter:∀x:Equiv.Perm (Fin 3),(∀y,y*x=x*y)→x=1:=by decide +kernel
  have hx:q xF=1:=hcenter _ hc
  have hxA:xF∈A:=by
    apply (QuotientGroup.eq_one_iff xF).mp
    apply e.injective
    exact hx.trans e.map_one.symm
  let a:p.A B5:=⟨((m.generator:p.parabolic):G),hxA⟩
  have ha:orderOf a=3:=by
    rw [←orderOf_coe]
    exact m.generator_ambient_order
  have hd:=orderOf_dvd_natCard a
  rw [ha,s.card_A p B5 hi] at hd
  norm_num at hd
end CFSG.Quasithin.ChapterJ.RuSubgroup.SecondCubicMarking
