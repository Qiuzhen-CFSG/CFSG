module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SmallClassification
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallActorLayers

/-!
# Matched chief quotient and offender types in the qrc source

Each noncentral chief factor of the original span has one of the four
small quotient actors. This module identifies its offender subgroup in
the same branch: S₃, S₃ × S₃, S₅ or S₅ × S₅, respectively. The solvable
branches use one common source factor count for the actor and its layer.
The symmetric-five branches use their actual single or paired marking.

The original qrc hypotheses discharge minimal parabolicity, the SQTK
cover, the FF witnesses and the small-action alternatives. The canonical
isomorphism from the action-kernel quotient to the faithful image retains
the chosen layer. The separate Thompson-image equality can therefore be
applied without choosing the ambient and layer types independently.

Source: Aschbacher–Smith, original 3.1.9(5), printed p.578, and 15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The literal chief quotient and offender subgroup have the matched source types. -/
theorem QrcHypotheses.sqtk_chief_small_actor_layer_types
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ChiefSmallActorLayerTypes (H ⧸ (actionHom (s.factorRepresentation i)).ker)
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation
          (s.factorRepresentation i))) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hff⟩ := h.sqtk_chief_ff_actor hG hM hu hJ hne hV hdual hq
  have hsmall := h.sqtk_chief_small_natural_alternatives hG hM hu hJ hne hV hdual hq hres
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  exact (minimalParabolic_chief_small_actor_layer_types (s.factorRepresentation i)
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S
    (source_intrinsic_minimalParabolic_of_notFF d hne (source_notFF_of_ratio_two d hq) S hS)
    ⟨_,(hff s i hi).1⟩ (hsmall s i hi).1).quotient_actor
end CFSG.Quasithin.Chapter3
