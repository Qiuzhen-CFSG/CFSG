module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesComponent

/-!
# The original local core in the larger span action

The restriction kernel of the centralizer-span projection to H lies in
O₂(H). Core lifting therefore identifies the image of O₂(H) with the
two-core of the H-image. This image fixes the original H-span modulo
⟨z⟩. If that span equals the full centralizer span, the image vanishes.
All maps and coordinates remain the original ones, even when the spans
are nonabelian. No normality of O₂(H) in C_G(z) is asserted.

Source: Aschbacher--Smith G.2.2 and 5.1.23, printed pp.332,645--646,
refs/quasithin.pdf. The Chapter 12 application locates the remaining
opposite-image centralizer factor in this exact local core image.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- The image of the original local two-core is the two-core of the image of H. -/
theorem LocalData.local_core_image (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis) :
    let π := SpanAction.projection s
    let J := (H.subgroupOf (centralizer ({z} : Set G))).map π
    ((H.pCoreIn 2).subgroupOf (centralizer ({z} : Set G))).map π = J.pCoreIn 2 := by
  intro π J
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  let f : H →* SpanAction.Actor s := π.comp (inclusion hHC)
  have hker : IsPGroup 2 f.ker :=
    pCore_isPGroup.to_le (d.restriction_kernel_le s hHC)
  let q : H →* f.range := f.rangeRestrict
  have hqker : IsPGroup 2 q.ker := by
    have he : q.ker = f.ker := by ext x; exact Subtype.ext_iff
    rw [he]
    exact hker
  have hq : (pCore 2 H).map q = pCore 2 f.range := by
    rw [← q.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hqker,
      map_comap_eq_self_of_surjective f.rangeRestrict_surjective]
  have hr : f.range = J := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion hHC a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hm : (pCore 2 H).map f = f.range.pCoreIn 2 := by
    have hh := congrArg (Subgroup.map f.range.subtype) hq
    rw [map_map] at hh
    exact hh
  rw [hr] at hm
  rw [← hm]
  ext x
  constructor
  · rintro ⟨a,⟨b,hb,he⟩,rfl⟩
    exact ⟨b,hb,congrArg π (Subtype.ext he)⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨inclusion hHC a,⟨a,ha,rfl⟩,rfl⟩

/-- The same local core image fixes the original H-span modulo the original point. -/
theorem LocalData.local_core_image_fixes_local_span (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis) :
    let Q := ((H.pCoreIn 2).subgroupOf (centralizer ({z} : Set G))).map
      (SpanAction.projection s)
    (SpanAction.conjugationSection s).imageSpace (setup T H C z).U ≤
      Representation.BinaryOffender.fixedSpace (SpanAction.representation s) Q := by
  intro Q v hv a
  obtain ⟨a',ha',he⟩ := a.property
  change SpanAction.representation s (a : SpanAction.Actor s) v = v
  rw [← he]
  apply (SpanAction.conjugationSection s).fixed_on_imageSpace_of_commutator_le
    (H.pCoreIn 2) (setup T H C z).U _ a' ha' v hv
  rw [commutator_comm]
  exact d.g2.commutator_U_core_le_point

/-- Equality of the two literal spans kills the whole local core image. -/
theorem LocalData.local_core_image_eq_bot_of_span_eq (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : (setup T H C z).U = (setup T (centralizer ({z} : Set G)) C z).U) :
    ((H.pCoreIn 2).subgroupOf (centralizer ({z} : Set G))).map
      (SpanAction.projection s) = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro a ha
  apply (SpanAction.projection_eq_one_iff s a).mpr
  intro u hu
  rw [← he] at hu
  exact d.g2.commutator_U_core_le_point (commutator_mem_commutator hu ha)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
