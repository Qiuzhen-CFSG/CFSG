module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalLineExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalCubicSylow

/-!
# The moved-line exclusion on the original Chapter 12 layer

The chosen module supplies the natural-layer, central-line factorization,
and uniqueness hypotheses for the source 6.2.7 moved-line contradiction.
Consequently the original field plane is disjoint from the commutator
plane. On the literal quotient this removes the disjointness premise from
the fixed-space family, minimal-offender theorem, and component model sieve.
All section coordinates and the original conjugate four-group are retained.

The remaining moved-plane model exclusions and 6.2.8 graph escape are still
needed for LocalAnalysis. No later recognition theorem is used here.
Source: Aschbacher--Smith, 6.2.7, pp.682--683, applied to 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource


open CFSG.Quasithin.Chapter6.Source
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
/-- Source 6.2.7's disjointness conclusion on the original Chapter 12 planes. -/
theorem source_local_one_sided_planes_disjoint
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    (B ⊓ centralizer (A : Set G)) ⊓ ⁅A,B⁆ = ⊥ := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  exact LocalFieldQuotientAction.one_sided_planes_disjoint h611 hnatural hE hfactor
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    g hBA hnon

/-- The original four-group is now a minimal best offender with moved plane
and fixed codimension two. The fixed-space family and component model sieve
have no extra disjointness premise. This is (*), (**), (!) and (!!) in 6.2.7. -/
theorem source_local_one_sided_plane_classification
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    letI := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
    LocalFieldQuotientAction.PlaneSection B A U := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  have hdis := source_local_one_sided_planes_disjoint D h h611 hnatural g hBA hnon
  obtain ⟨ρ,c,hfaith,hI,hquad,hIc,hm,_,_,hcases,hclass,_,_,hmark⟩ :=
    LocalFieldQuotientAction.exists_classified_offender_action h611 hnatural hE hfactor g hBA hnon
  have hdim := (hcases.resolve_right (by
    intro hc
    have he := hc.1
    rw [hdis,card_bot] at he
    contradiction)).2
  obtain ⟨hcodim,hfamily,hmin,hcomponents⟩ := hclass hdis
  unfold LocalFieldQuotientAction.PlaneSection
  refine ⟨ρ,c,hfaith,hI,hquad,hIc,hm,hdim,hcodim,hfamily,hmin,?_,hmark⟩
  intro K hK hKI
  exact ⟨(hcomponents K hK hKI).1,
    source_local_one_sided_action_component_models D h h611 hnatural g hBA hnon K hK
      (hcomponents K hK hKI).2⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
