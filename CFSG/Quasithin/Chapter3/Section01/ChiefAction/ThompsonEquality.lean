module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.PairThompsonLower
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.ThompsonUpper
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallOffenderCentralizer

/-!
# The literal global Thompson image on every source chief factor

The source's selected maximum elementary subgroup gives the lower inclusion:
its offender image normally generates the whole small offender base. For the
upper inclusion, quadratic replacement inside AU supplies a chief offender
inside every moving maximum subgroup's image. That elementary image commutes
with the contained offender, whose centralizer lies in the small base.
Conjugate-span generation then gives the original global Thompson image.

Both inclusions use the literal chief action homomorphism and the original
J(H). The small models and all offender-centralizer premises are discharged
from the original qrc assumptions and the residual-centralizer hypothesis.

Source: Aschbacher–Smith, original 3.1.9(5), printed p.578, used by
original 15.1.12(3), printed p.1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_chief_thompson_image_eq
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
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (actionHom (s.factorRepresentation i)) =
        offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
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
  have hl := h.sqtk_chief_offenderSubgroup_le_thompson_image hG hM hu hJ hne hV hdual hq hres
  have hupp := h.sqtk_chief_thompson_image_le_of_offender_centralizers hG hM hu hJ hne hV hdual hq
  have hc := h.sqtk_chief_small_natural_alternatives hG hM hu hJ hne hV hdual hq hres
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  apply le_antisymm ?_ (hl s i hi)
  apply hupp s i hi
  intro B hB
  exact minimalParabolic_small_chief_offender_centralizer_le
    (s.factorRepresentation i) S hp (hc s i hi).1 hB
end CFSG.Quasithin.Chapter3
