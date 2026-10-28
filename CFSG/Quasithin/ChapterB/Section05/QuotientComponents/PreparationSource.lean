module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.FixedCore
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ComponentStructure
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ChiefSections
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.PrimeCores

/-!
# The complete B.5.5 preparation from earlier source theorems

Offender generation and B.1.5(4) make every component normal and supply a
moving original best offender. The fixed-core reduction proves the whole
fixed-space clause for every such offender. Choosing a minimal offender in
that action image and lifting it with equal weight gives an original best
offender and a faithful invariant chief section. A.2 and A.3.6 supply the
component's SQTK property and center alternatives; the corrected B.4.2
classifies the literal chief-section actor and yields the full component list.
The independent solvable argument proves non-three prime-core centrality
and the exact generalized-Fitting identity.

`source_lemma_B_5_5` assembles every field of the existing
`Preparation.ComponentConclusion` under the unchanged B.5.3 hypothesis;
`componentInput` supplies its universal implication. Neither nontriviality
of the actor nor a nonzero module is required. The only explicit earlier
inputs are full B.1.5(4), A.2, A.3.6 and corrected B.4.2, produced by
`qt-b01-component-normalization`, `qt-a-02`, `qt-a03-sqtk-structure` and
`qt-b-04`. Their discharge remains with `qt-b05-quotient-components`.
The `PreparationSource.Application` descendant removes the previously
assumed B.5.5 input from the existing B.5.6 cover construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5, printed pp.104–105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions
universe u v

/-- Every clause of B.5.5 follows from the precise earlier universal source
theorems. The existential chief section retains the same original offender
and literal quotient throughout its fitting, offender, model and action fields. -/
theorem source_lemma_B_5_5
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v})
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) : Preparation.ComponentConclusion ρ := by
  let := hyp.finite_module
  obtain ⟨hcentral, hfitting⟩ := source_lemma_B_5_5_2 ρ hyp
  refine {
    normal := fun L hL => component_normal ρ hn hyp hL
    moving := fun L hL => component_moving ρ hn hyp hL
    fixedCore := ?_
    chief := ?_
    primeCore_central := hcentral
    fitting := hfitting }
  · intro L hL A hbest hm
    let := component_normal ρ hn hyp hL
    let := hL.2
    exact fixedCore ρ hyp.faithful hyp.twoCore L A hm hbest
  · intro L hL
    let := component_normal ρ hn hyp hL
    obtain ⟨A₀, hbest, hm⟩ := component_moving ρ hn hyp hL
    exact chief ρ hA h36 h4 hyp hL hbest hm

/-- The full universal B.5.5 implication consumed by the existing B.5.6
preparation route, with only its genuine earlier source implications explicit. -/
theorem componentInput {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v})
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} K) :
    Preparation.ComponentInput.{u,v} K := by
  intro D _ _ V _ _ ρ hyp
  exact source_lemma_B_5_5 ρ hn hA h36 h4 hyp

end CFSG.Quasithin.ChapterB.PreparationSource
