module
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality

/-!
# Sharp offenders on the original two chief modules

The same minimal maximum elementary actor selected in3.1.9(2) has kernel
A∩O₂(H) on every noncentral chief factor. The literal rank equalities of
3.1.9(3) therefore make its faithful image an FF offender with equal rank
and fixed codimension. No offender or representation witness is assumed.

Source: Aschbacher–Smith3.1.9(5), printed pp.577–578, applied in15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_chief_ff_actor
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
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H ∧
      ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A) ∧
        rank (actionSubgroup (s.factorRepresentation i) A) =
          fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            (actionSubgroup (s.factorRepresentation i) A) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hquad,hmin,heq⟩ :=
    h.sqtk_minimal_actor_equalities hG hM hu hJ hne hV hdual hq
  refine ⟨A,hA,hAR,?_⟩
  intro s i hi
  let : IsElementaryAbelian 2 A := hA.2.1
  have hk := MultipleFactors.source_chief_sylow_kernel U S
    (source_intrinsic_minimalParabolic_of_notFF d hne (source_notFF_of_ratio_two d hq) S hS)
    s i hi A hA.1
  have hn : ¬ A ≤ (s.factorRepresentation i).ker := by
    intro hn
    apply hAR
    have he : A ⊓ (s.factorRepresentation i).ker = A := inf_eq_left.mpr hn
    rw [he] at hk
    exact hk.le.trans inf_le_right
  have hidx : (s.factorRepresentation i).ker.relIndex A = (pCore 2 H).relIndex A := by
    rw [←inf_relIndex_left,hk,inf_relIndex_left]
  have he : rank (actionSubgroup (s.factorRepresentation i) A) =
      fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) := by
    rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,hidx]
    exact (heq s).2.2.2.2.1 i hi
  exact ⟨⟨elementary_actionSubgroup _ hn,he.ge⟩,he⟩



end CFSG.Quasithin.Chapter3
