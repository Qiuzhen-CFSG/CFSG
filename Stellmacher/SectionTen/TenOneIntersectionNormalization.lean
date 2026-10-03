module
public import Stellmacher.SectionTen.TenOneCommonIntersection

/-!
# Normalization transfer inside the common neighbor intersection

Let L contain the actual middle center and lie in the common intersection
of the first and terminal modules. If the middle two-core normalizes L,
then the full middle stabilizer normalizes it. Only actual subgroup
containments and two-core normalization are supplied.

The penultimate join-action theorem shows that the two endpoint cores
normalize L enlarged by the middle center, which is L itself. Their join
contains the middle residual. The middle-edge core product and the
residual/Sylow supplement combine this with the given middle-core action.

This is the local normalization step for the enlarged selected displacement
in Stellmacher (10.1)(13), printed p.63 of
`refs/files/stellmacher-n-group.pdf`.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_intersection_subgroup_normalized
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (L : Subgroup G)
    (hZL : ZAt ctx.Γ middle ≤ L)
    (hLI : L ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a')
    (hQL : QAt ctx.Γ middle ≤ Subgroup.normalizer (L : Set G)) :
    GAt ctx.Γ middle ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1,ctx.Γ.act_one _⟩).2
  have hfirstOffset : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length-2) ctx.criticalPath.firstStep := by
    refine ⟨⟨1, by rw [ctx.critical_length]; decide⟩,?_,?_⟩
    · simp [ctx.critical_length]
    · exact ctx.criticalPath.path_first
  have hpen : ctx.criticalPath.path ⟨ctx.criticalPath.length-1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = middle := by
    obtain ⟨index,hindex,rfl⟩ := hpath
    apply congrArg ctx.criticalPath.path
    apply Fin.ext
    change ctx.criticalPath.length - 1 = index.val
    have hlength := ctx.critical_length
    omega
  have hjoin : QAt ctx.Γ ctx.criticalPath.firstStep ⊔ QAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.normalizer (L : Set G) := by
    have hh := (nine_five_penultimate_join_action_of_initial_four
      ctx.toAmbientSectionNineContext hfour hb ctx.criticalPath.firstStep hfirstOffset L hLI).2
    rw [hpen,sup_eq_left.mpr hZL] at hh
    exact hh
  have hEL : EAt ctx.Γ middle ≤ Subgroup.normalizer (L : Set G) := by
    have hh := nine_five_penultimate_residual_le_join_of_initial_four
      ctx.toAmbientSectionNineContext hfour hb ctx.criticalPath.firstStep hfirstOffset
    rw [hpen] at hh
    exact hh.trans hjoin
  have hedge : GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (L : Set G) := by
    rw [← ten_one_middle_edge_core_product ctx middle hpath]
    exact sup_le hQL (le_sup_left.trans hjoin)
  let sylow : Sylow 2 (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) := default
  have hsylow := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
    ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) sylow).1
  have hsupp : EAt ctx.Γ middle ⊔ sylowTwoAmbient _ sylow = GAt ctx.Γ middle := by
    change ctx.Γ.twoResidualAt middle ⊔ _ = _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow hsylow
  rw [← hsupp]
  exact sup_le hEL ((Subgroup.map_subtype_le _).trans hedge)
end Stellmacher.SectionTen
