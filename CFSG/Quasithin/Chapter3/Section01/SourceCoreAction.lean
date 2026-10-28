module
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality

/-!
# Nontrivial core action on the original SQTK orbit span

The two sharp SQTK equalities identify the fixed codimension of a moving
maximum elementary actor both with twice its rank modulo the two-core and
with twice the rank of its core intersection acting on the whole span.
The former rank is positive. Consequently the core acts nontrivially on
the span, although it acts trivially on the irreducible chief factors.
This retains extension information that is lost on the associated factors.

Source: Aschbacher--Smith 3.1.9(2--3) and 15.1.12(1--2),
printed pp.576--577 and 1089--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The intrinsic two-core moves the literal elementary orbit span. -/
theorem QrcHypotheses.sqtk_core_not_centralizes_span
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    ¬ pCore 2 H ≤ centralizer ((conjugateSpan H V).subgroupOf H : Set H) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  obtain ⟨A,hA,hAR,hquad,hmin,heq⟩ :=
    h.sqtk_minimal_actor_equalities hG hM hu hJ hne hV hdual hq
  let : IsElementaryAbelian 2 A := hA.2.1
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hpos := MultipleFactors.quotient_rank_pos A (pCore 2 H) hAR
  have hfirst := (heq s).2.1
  have hsecond := (heq s).2.2.1
  intro hc
  have hb : A ⊓ pCore 2 H ≤ centralizer (U : Set H) := inf_le_right.trans hc
  rw [relIndex_eq_one.mpr hb] at hsecond
  norm_num at hsecond
  omega

end CFSG.Quasithin.Chapter3
