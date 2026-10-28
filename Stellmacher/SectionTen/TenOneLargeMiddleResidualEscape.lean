module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Stellmacher.SectionNine.NineFivePenultimateCoreEscapeReduction
public import Stellmacher.SectionTen.TenOneMiddleResidualQuotientThree

/-!
# The middle residual core escapes the large generated neighborhood

In the original Section Ten no-transvection configuration, the middle
residual two-core is not contained in the generated middle neighborhood.
No terminal core-index bound or desired middle quotient order is assumed.

The common endpoint-module intersection I is middle-normal, has order
eight, and centralizes the generated neighborhood. If the middle residual
two-core lay in that neighborhood, it would act trivially on I. The actual
residual conjugation action would then factor through its three-group
quotient. Its fixed subgroup is trivial by the original residual-centralizer
conclusion (7.5)(c), since I lies in the middle core. Orbit counting for a
three-group acting on eight elements contradicts that trivial fixed subgroup.
All actions are the literal subgroup conjugation and its automorphism image.

This gives the nontrivial middle residual image needed for Stellmacher
(10.1)(b2), printed pp.60,65, using the source-(14) intersection order and the
standing middle SL₂(2) quotient. It also isolates the large-case obstruction
to the small-case residual-neighborhood containment.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

public theorem ten_one_large_middle_residual_core_not_le_neighborhood
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ¬ twoCoreIn (EAt ctx.Γ middle) ≤ GeneratedNeighborhoodV ctx.Γ middle := by
  let M := GAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let U := twoCoreIn E
  let N := GeneratedNeighborhoodV ctx.Γ middle
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a'
  intro hUN
  have hthree := ten_one_middle_residual_quotient_isThreeGroup ctx middle hpath
  have hE : E = twoResidualIn M := ctx.Γ.twoResidualAt_def _
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hMI : M ≤ normalizer (I:Set G) := ten_one_common_intersection_normalized ctx middle hpath
  have hIC : I ≤ centralizer (U:Set G) :=
    (ten_one_common_intersection_centralizes ctx middle hpath).trans (centralizer_le hUN)
  have hUC : U ≤ centralizer (I:Set G) := le_centralizer_iff.mp hIC
  have hIQ : I ≤ QAt ctx.Γ middle := by
    have hIN : I ≤ N := inf_le_left.trans (le_sSup
      ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr (sectionTenOpeningGeometry ctx middle hpath).2.1,rfl⟩)
    exact hIN.trans (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
      (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length];decide) middle)
  let _ : MulDistribMulAction E I := conjMulDistribMulActionOfLeNormalizer E I (hEM.trans hMI)
  let action := MulDistribMulAction.toMulAut E I
  have hker : pCore 2 E ≤ action.ker := by
    intro actor hactor
    apply MonoidHom.mem_ker.mpr
    ext point
    change (actor:G) * (point:G) * (actor:G)⁻¹ = (point:G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hUC (mem_map_of_mem E.subtype hactor)) point point.property).symm
  let descended : (E ⧸ pCore 2 E) →* action.range := QuotientGroup.lift _ action.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hker)
  have hsurj : Function.Surjective descended := by
    intro actor
    obtain ⟨native,rfl⟩ := action.rangeRestrict_surjective actor
    exact ⟨QuotientGroup.mk' (pCore 2 E) native,rfl⟩
  have hactionThree : IsPGroup 3 action.range := hthree.of_surjective descended hsurj
  have hfixed : FixedPoints.subgroup action.range I = ⊥ := by
    apply bot_unique
    intro point hpoint
    change point = 1
    apply Subtype.ext
    have hcentral : (point:G) ∈ centralizer (E:Set G) := by
      rw [mem_centralizer_iff]
      intro actor hactor
      have hh := hpoint ⟨action ⟨actor,hactor⟩,⟨⟨actor,hactor⟩,rfl⟩⟩
      have hv := congrArg Subtype.val hh
      change actor * (point:G) * actor⁻¹ = (point:G) at hv
      exact mul_inv_eq_iff_eq_mul.mp hv
    exact (nine_five_initial_orbit_residual_centralizer ctx.toLocalContext.toSectionNineLocalContext
      middle (sectionTenOpeningGeometry ctx middle hpath).1).le ⟨hIQ point.property,hcentral⟩
  have hIcard : Nat.card I = 8 := (ten_one_large_terminal_structure ctx middle hpath hno).2.2
  have hmod := hactionThree.card_modEq_card_fixedPoints I
  change Nat.ModEq 3 (Nat.card I) (Nat.card (FixedPoints.subgroup action.range I)) at hmod
  rw [hIcard,hfixed,card_bot] at hmod
  norm_num [Nat.ModEq] at hmod

end Stellmacher.SectionTen
