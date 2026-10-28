module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Flag
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# The second Ru core and its literal line-radical image

The source group L₂T equals N_L(V₂). Its original quotient has kernel S
and is a conjugate line parabolic. Lifting the two-core therefore identifies
R₂/S with the actual conjugate four-group and gives |R₂| = 2¹³. The quotient
map is the restriction of the original Ru1 map throughout.

Source: Aschbacher–Smith, J.4 opening notation and J.4.3(1), printed pp.440–441.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree Matrix.PSL3Two
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The source second two-core O₂(L₂T), inside G. -/
def Plane.R₂ : Subgroup G := (p.L₂ ⊔ (d.T : Subgroup G)).pCoreIn 2

/-- The second core is the actual core of the plane normalizer. -/
theorem Plane.R₂_eq : p.R₂ = p.parabolic.pCoreIn 2 := by
  unfold Plane.R₂
  rw [p.residual_sup_sylow]

/-- Restriction of the original Ru1 quotient to the actual plane normalizer. -/
def Plane.parabolicMap : p.parabolic →* Group := d.ru1.quotientMap.comp
  (inclusion (fun _ h => ((p.mem_parabolic _).mp h).1))

/-- The restricted map evaluates through the original Ru1 quotient. -/
theorem Plane.parabolicMap_apply (b : p.parabolic) :
    p.parabolicMap b = d.ru1.quotientMap
      ⟨b,((p.mem_parabolic _).mp b.property).1⟩ := by
  rfl

/-- The actual range is the original subgroup image. -/
theorem Plane.parabolicMap_range : p.parabolicMap.range =
    (p.parabolic.subgroupOf d.L).map d.ru1.quotientMap := by
  ext a
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨⟨l,((p.mem_parabolic _).mp l.property).1⟩,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

/-- The second quotient is a literal conjugate line parabolic. -/
theorem Plane.parabolicMap_range_conj : ∃ g : Group,
    p.parabolicMap.range = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  rw [p.parabolicMap_range]
  exact p.parabolic_image

/-- The source second parabolic quotient is S₄. -/
def Plane.parabolicImageEquivS4 : p.parabolicMap.range ≃* Equiv.Perm (Fin 4) := by
  let g := Classical.choose p.parabolicMap_range_conj
  have hg := Classical.choose_spec p.parabolicMap_range_conj
  exact (MulEquiv.subgroupCongr hg).trans
    ((lineParabolicSL.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans MarkedAutomorphisms.lineEquivSymmetric)

/-- The original special core lies in the actual second parabolic. -/
theorem Plane.S_le_parabolic : d.toTypeRuSetup.S ≤ p.parabolic :=
  d.S_le_T.trans p.sylow_le_parabolic

/-- The kernel of the restricted quotient is precisely the original S. -/
theorem Plane.parabolicMap_kernel : p.parabolicMap.ker =
    d.toTypeRuSetup.S.subgroupOf p.parabolic := by
  ext a
  change d.ru1.quotientMap ⟨a,((p.mem_parabolic _).mp a.property).1⟩ = 1 ↔ _
  change (⟨a,((p.mem_parabolic _).mp a.property).1⟩ : d.L) ∈ d.ru1.quotientMap.ker ↔ _
  rw [d.ru1.quotient_kernel]
  rfl

private theorem kernel_pGroup : IsPGroup 2 p.parabolicMap.ker := by
  rw [p.parabolicMap_kernel]
  exact (isPGroup_pCoreIn 2 d.L).comap_subtype

/-- The second core has the source order 2¹³. -/
theorem Plane.card_R₂ : Nat.card p.R₂ = 8192 := by
  rw [p.R₂_eq, pCoreIn, card_map_of_injective p.parabolic.subtype_injective]
  have hk : IsPGroup 2 p.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_pGroup p
  rw [p.parabolicMap.rangeRestrict.card_pCore_of_ker_isPGroup
    p.parabolicMap.rangeRestrict_surjective hk,MonoidHom.ker_rangeRestrict,
    p.parabolicMap_kernel,
    Nat.card_congr (subgroupOfEquivOfLe p.S_le_parabolic).toEquiv,
    d.ru1.card_S,(ParabolicCoreModel.core_data p.parabolicImageEquivS4).2]

/-- The two-core image is the concrete conjugate four-group in the original quotient. -/
theorem Plane.core_image : ∃ g : Group,
    (pCore 2 p.parabolic).map p.parabolicMap = R.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := p.parabolicMap_range_conj
  have hk : IsPGroup 2 p.parabolicMap.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_pGroup p
  have he := p.parabolicMap.rangeRestrict.comap_pCore_of_ker_isPGroup
    p.parabolicMap.rangeRestrict_surjective hk
  have hm : (pCore 2 p.parabolic).map p.parabolicMap.rangeRestrict =
      pCore 2 p.parabolicMap.range := by
    rw [← he,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ p.parabolicMap.rangeRestrict_surjective]
    exact le_top
  have hh := congrArg (fun A : Subgroup p.parabolicMap.range =>
    A.map p.parabolicMap.range.subtype) hm
  rw [map_map] at hh
  change (pCore 2 p.parabolic).map p.parabolicMap = p.parabolicMap.range.pCoreIn 2 at hh
  rw [hg,← map_pCoreIn_of_injective 2 lineParabolicSL (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective,lineParabolicSL_pCoreIn_two_eq_R] at hh
  exact ⟨g,hh⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
