module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Classification
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallActors

/-!
# The four original chief centralizer quotients

The kernel of the actual chief action is its centralizer. Its quotient is
canonically the faithful image already classified by `Classification`.
The result gives the source's four named actors S₃, S₃≀C₂, S₅, S₅≀C₂ on
these literal quotients, while `Classification` retains their natural action
coordinates on the full chief factors.

Source: Aschbacher–Smith, original 3.1.9(5) and 15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_chief_small_quotient
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
      ChiefSmallActor (H ⧸ (actionHom (s.factorRepresentation i)).ker) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hc := h.sqtk_chief_small_whole_action hG hM hu hJ hne hV hdual hres hq
  dsimp only
  intro s i hi
  exact (hc s i hi).quotient_actor
end CFSG.Quasithin.Chapter3
