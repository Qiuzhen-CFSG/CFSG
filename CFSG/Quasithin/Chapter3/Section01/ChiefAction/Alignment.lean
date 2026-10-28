module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Offender
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.Kernel

/-!
# The common actor on the original nonsolvable chief factors

The same source actor offends sharply on every noncentral chief factor.
The nonsolvable minimal-parabolic kernel theorem identifies each literal
conjugation kernel with the original canonical core. This is the actor
alignment in3.1.9(5); comparison of its different natural modules is separate.
Source: Aschbacher–Smith3.1.9, printed pp.577–578, used in15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_nonsolvable_chief_kernels
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hs : ¬ Group.IsSolvable H) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ∀ (t : SeriesOn U) (j : Fin t.series.length), ¬ t.Central j →
        (s.factorRepresentation i).ker = (t.factorRepresentation j).ker := by
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
  dsimp only
  intro s i hi t j hj
  let := s.factorRepresentation_irreducible i
  let := t.factorRepresentation_irreducible j
  have hsq := sqtk_of_mem_H hG h.right_mem.1.1.1
  exact (ChapterB.minimalParabolic_nonsolvable_chief_kernel (s.factorRepresentation i)
    hsq S hp hs ⟨_,(hff s i hi).1⟩).trans
    (ChapterB.minimalParabolic_nonsolvable_chief_kernel (t.factorRepresentation j)
      hsq S hp hs ⟨_,(hff t j hj).1⟩).symm

end CFSG.Quasithin.Chapter3
