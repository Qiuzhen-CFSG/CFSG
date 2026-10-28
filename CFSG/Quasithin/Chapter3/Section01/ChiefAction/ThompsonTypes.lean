module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.ThompsonEquality
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.ActorLayers

/-!
# Matched chief quotient and original Thompson image

The literal image of J(H) equals the offender subgroup on each noncentral
chief factor. Transporting the matched actor/offender classification along
this equality gives the source's four respective pairs of group types.

Source: Aschbacher–Smith, original 3.1.9(5), printed p.578, and 15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The chief quotient and the image of the original J(H) have the four
matched types asserted by the source. -/
theorem QrcHypotheses.sqtk_chief_thompson_actor_layer_types
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
      ChiefSmallActorLayerTypes (H ⧸ (actionHom (s.factorRepresentation i)).ker)
        ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map
          (actionHom (s.factorRepresentation i))) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  have htypes := h.sqtk_chief_small_actor_layer_types hG hM hu hJ hne hV hdual hres hq
  have heq := h.sqtk_chief_thompson_image_eq hG hM hu hJ hne hV hdual hq hres
  dsimp only
  intro s i hi
  exact (htypes s i hi).of_subgroup_eq (heq s i hi)

end CFSG.Quasithin.Chapter3
