module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Offender
public import CFSG.Quasithin.ChapterB.Section02.QuadraticSubactor

/-!
# Offenders inside every moving maximum chief image

A maximum elementary subgroup outside the two-core need not itself be
quadratic on the entire span. Replace it inside its join with that span by
an equal-order quadratic subgroup. The source rank equalities apply to
this replacement on each noncentral chief. Since the elementary normal
span acts trivially on its own chief factors, its offender image remains
inside the original maximum subgroup's image.

This supplies the precise input for the paired Thompson upper bound in
Aschbacher–Smith 3.1.9(5), printed p.578, without asserting rank equality
for arbitrary maximum elementary subgroups.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
theorem QrcHypotheses.sqtk_chief_max_contains_offender
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    let S := T.subtype h.right_mem.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H →
      ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        ∃ B : Subgroup (actionImage (s.factorRepresentation i)),
          IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) B ∧
          B ≤ actionSubgroup (s.factorRepresentation i) A := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    exact ht
  have hUR : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x,hx,he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  have hP := source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS
  dsimp only
  intro A hA hAR s i hi
  have hAnc : ¬ A ≤ centralizer (U : Set H) := fun hc =>
    hAR ((le_inf hA.1 hc).trans (source_span_centralizer_sylow_le_core d hne hV hnf S hS))
  obtain ⟨D,hD,hDnc,hquad,hDA⟩ := ChapterB.maxElementary_exists_quadratic_subactor U S A hUS hA hAnc
  let : IsElementaryAbelian 2 D := hD.2.1
  have hDR : ¬ D ≤ pCore 2 H := fun hd =>
    hDnc (source_max_actor_in_core_centralizes d hnf S hS D hD hd)
  have hc := h.sqtk_noncentral_count_two hG hM hu hJ hne hV hdual hq s
  have heq := source_sqtk_multiple_equalities d hne hV
    (sqtk_of_mem_H hG h.right_mem.1.1.1) hq S hS s (by omega) D hD hquad hDnc
  have hk := MultipleFactors.source_chief_sylow_kernel U S hP s i hi D hD.1
  have hn : ¬ D ≤ (s.factorRepresentation i).ker := by
    intro hn
    apply hDR
    rw [inf_eq_left.mpr hn] at hk
    exact hk.le.trans inf_le_right
  have hidx : (s.factorRepresentation i).ker.relIndex D = (pCore 2 H).relIndex D := by
    rw [←inf_relIndex_left,hk,inf_relIndex_left]
  have he : rank (actionSubgroup (s.factorRepresentation i) D) =
      fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) D) := by
    rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,hidx]
    exact heq.2.2.2.2.1 i hi
  refine ⟨actionSubgroup (s.factorRepresentation i) D,⟨elementary_actionSubgroup _ hn,he.ge⟩,?_⟩
  have hUk : U ≤ (s.factorRepresentation i).ker := by
    have hh := MultipleFactors.source_chief_sylow_kernel U S hP s i hi U hUS
    rw [inf_eq_left.mpr hUR] at hh
    exact hh.ge.trans inf_le_right
  have hm : U.map (actionHom (s.factorRepresentation i)) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff U).mpr
    rwa [actionHom_ker_eq]
  change D.map (actionHom (s.factorRepresentation i)) ≤ A.map _
  have hmap := map_mono (f := actionHom (s.factorRepresentation i)) hDA
  simpa only [Subgroup.map_sup,hm,sup_bot_eq] using hmap
end CFSG.Quasithin.Chapter3
