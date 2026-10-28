module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Elementary
public import Theory.Representation.PSL3Two.SteinbergStructure.LineRadicalCommutator.Cubic
public import Theory.GroupAction.CentralElementaryQuotientOrbit.Cubic

/-!
# A fixed-free cubic action on the actual second core quotient

The same conjugate line-parabolic marking identifies both the actual R₂ image
and a cubic actor. Fixedness on R₂/S forces an element into S by the S₄ core
action. On S/S₂ the literal Steinberg coordinate calculation then forces it
into S₂. Thus the lifted actor is fixed-free on the original R₂/S₂.

Source: Aschbacher–Smith, J.4.4(2), printed p.441.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree Matrix.PSL3Two
open BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

private theorem core_image_range : p.secondImage=p.parabolicMap.range.pCoreIn 2 := by
  have hk : IsPGroup 2 p.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,p.parabolicMap_kernel]
    exact (isPGroup_pCoreIn 2 d.L).comap_subtype
  have hm : (pCore 2 p.parabolic).map p.parabolicMap.rangeRestrict=
      pCore 2 p.parabolicMap.range := by
    rw [← p.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
      p.parabolicMap.rangeRestrict_surjective hk,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ p.parabolicMap.rangeRestrict_surjective]
    exact le_top
  have h := congrArg (fun K:Subgroup p.parabolicMap.range =>
    K.map p.parabolicMap.range.subtype) hm
  rw [map_map] at h
  exact p.secondImage_eq.trans h

private theorem rangeMap_eq_one (a:p.parabolic) :
    p.parabolicMap.rangeRestrict a=1 ↔ (a:G)∈d.toTypeRuSetup.S := by
  change a∈p.parabolicMap.rangeRestrict.ker ↔ _
  rw [MonoidHom.ker_rangeRestrict,p.parabolicMap_kernel]
  rfl

private theorem rangeMap_mem_core (a:p.parabolic) (ha:(a:G)∈p.R₂) :
    p.parabolicMap.rangeRestrict a∈pCore 2 p.parabolicMap.range := by
  have h := mem_map_of_mem p.parabolicMap
    (show a∈pCore 2 p.parabolic from by
      have he : p.R₂.subgroupOf p.parabolic=pCore 2 p.parabolic := by
        rw [p.R₂_eq]; exact comap_map_eq_self_of_injective p.parabolic.subtype_injective _
      rw [← he]; exact ha)
  rw [← p.secondImage_eq,core_image_range] at h
  obtain ⟨b,hb,he⟩ := h
  exact (Subtype.ext he : b=p.parabolicMap.rangeRestrict a) ▸ hb

/-- A cubic image in the original Ru1 quotient acts fixed freely on R₂/S₂. -/
theorem Plane.exists_second_cubic_lift :
    ∃ c:p.parabolic,orderOf (p.parabolicMap c)=3 ∧
      ∀ a:p.parabolic,(a:G)∈p.R₂ → ((⁅c,a⁆:p.parabolic):G)∈p.S₂ → (a:G)∈p.S₂ := by
  obtain ⟨g,hg⟩ := p.parabolicMap_range_conj
  have hR : p.secondImage=R.map (MulAut.conj g).toMonoidHom := by
    rw [core_image_range,hg,← map_pCoreIn_of_injective 2 _
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      lineParabolicSL_pCoreIn_two_eq_R]
  have hm : g*lineCubic*g⁻¹∈p.parabolicMap.range := by
    rw [hg]
    exact ⟨lineCubic,lineCubic_mem,rfl⟩
  obtain ⟨c,hc⟩ := hm
  have ho : orderOf (p.parabolicMap c)=3 := by
    rw [hc]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _).trans lineCubic_order
  refine ⟨c,ho,fun a ha hcomm => ?_⟩
  have hfa : p.parabolicMap.rangeRestrict c * p.parabolicMap.rangeRestrict a *
      (p.parabolicMap.rangeRestrict c)⁻¹=p.parabolicMap.rangeRestrict a := by
    have he := (rangeMap_eq_one p ⁅c,a⁆).mpr (p.S₂_le_S hcomm)
    rw [map_commutatorElement,commutatorElement_def] at he
    exact mul_inv_eq_one.mp he
  have has : (a:G)∈d.toTypeRuSetup.S := by
    apply (rangeMap_eq_one p a).mp
    exact ParabolicCoreModel.core_cubic_fixed p.parabolicImageEquivS4 _
      (by rw [← orderOf_coe]; exact ho) _ (rangeMap_mem_core p a ha) hfa
  let x:d.toTypeRuSetup.S := ⟨a,has⟩
  let l:d.L := ⟨c,((p.mem_parabolic _).mp c.property).1⟩
  let y:d.toTypeRuSetup.S := ⟨(c:G)*(a:G)*(c:G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) a).mp has⟩
  have hxy : ((y*x⁻¹:d.toTypeRuSetup.S):G)∈p.S₂ := hcomm
  have hd := (p.mem_S₂ (y*x⁻¹)).mp hxy
  have he : (d.ru1.steinberg.coordinates (y*x⁻¹)).toAdd=
      S (p.parabolicMap c) (d.ru1.steinberg.coordinates x).toAdd-
        (d.ru1.steinberg.coordinates x).toAdd := by
    rw [map_mul,map_inv]
    change (d.ru1.steinberg.coordinates y).toAdd+
      -(d.ru1.steinberg.coordinates x).toAdd=_
    rw [d.ru1.steinberg.equivariant l x,p.parabolicMap_apply]
    exact (sub_eq_add_neg
      (S (d.ru1.quotientMap l) (d.ru1.steinberg.coordinates x).toAdd)
      (d.ru1.steinberg.coordinates x).toAdd).symm
  rw [he,p.steinbergCommutator_eq_image,hR,hc] at hd
  apply (p.mem_S₂ x).mpr
  rw [p.steinbergCommutator_eq_image,hR]
  exact conjugate_lineCubic_fixed_mod_commutator g _ hd

end CFSG.Quasithin.ChapterJ.RuSubgroup
