module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBinaryExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalLineExclusion

/-!
# Removing the binary linear-three component on the original Chapter 12 quotient

The actual plane-offender section already supplies minimality, the moved
plane, and Irr⁺ for each component moved by that offender. The original
field-normalizer cubic now excludes PSL₃(2), leaving only A5 and SL₃(4).
All quotient maps and the marking of the conjugate layer are unchanged.

The remaining two model exclusions and the 6.2.8 graph escape are still
required for LocalAnalysis. Source: Aschbacher--Smith 6.2.7, pp.682--684,
applied to the original layer in 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original plane section, now with only the A5 and SL₃(4) component
models. The PSL₃(2) exclusion has no extra placement or module premise. -/
theorem source_local_one_sided_plane_two_models
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
    LocalFieldQuotientAction.PlaneTwoModelSection B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  obtain ⟨ρ,c,hf,hI,hq,hIc,hm,hd,hcodim,hfam,hmin,hmodels,hmark⟩ :=
    source_local_one_sided_plane_classification D h h611 hnatural g hBA hnon
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  unfold LocalFieldQuotientAction.PlaneTwoModelSection
  refine ⟨ρ,c,hf,hI,hq,hIc,hm,hd,hcodim,hfam,hmin,?_,hmark⟩
  intro K hK hKI
  obtain ⟨hirr,hcases⟩ := hmodels K hK hKI
  refine ⟨hirr,?_⟩
  rcases hcases with hA | hB | hS
  · exact Or.inl hA
  · exact (LocalFieldQuotientAction.one_sided_binary_component_excluded
      h611 hnatural hE hfactor
      (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
      g hBA hnon ρ c hf hmin K hK hKI hirr hB).elim
  · exact Or.inr hS

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
