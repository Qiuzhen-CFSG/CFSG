module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.PairThompsonLower
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SmallClassification

/-!
# The original global Thompson image contains every small chief base

The same maximum elementary subgroup supplied by the source offends on each
original noncentral chief factor. Its image belongs to the image of the
original global elementary Thompson subgroup. The latter is normal, so the
small-action normal-generation theorem puts the entire offender base inside
it. The original field-exclusion theorem supplies every small-action premise.

This is the lower inclusion for the original Thompson-image equality in
Aschbacher–Smith 3.1.9(5), printed pp.577–578, used in 15.1.12(3).
The original subgroup J(H), each original chief factor, and their actual
quotient action maps are retained throughout.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_chief_offenderSubgroup_le_thompson_image
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G)) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ≤
        (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (actionHom (s.factorRepresentation i)) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hp := source_intrinsic_minimalParabolic_of_notFF d hne
    (source_notFF_of_ratio_two d hq) S hS
  obtain ⟨A,hA,hAR,hff⟩ := h.sqtk_chief_ff_actor hG hM hu hJ hne hV hdual hq
  have hc := h.sqtk_chief_small_natural_alternatives hG hM hu hJ hne hV hdual hq hres
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  exact chief_small_offenderSubgroup_le_thompson_image (s.factorRepresentation i) S hp
    A hA (hff s i hi).1 (hc s i hi).1
end CFSG.Quasithin.Chapter3
