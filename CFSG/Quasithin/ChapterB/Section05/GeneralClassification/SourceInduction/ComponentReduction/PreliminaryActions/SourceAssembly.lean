module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.PreparedApplication
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Context

/-!
# Preliminary B.5.9 classification from the earlier source implications

The full B.5.5 implication gives component normality and the faithful action
on the fixed space of O₂(LA). Preparation constructs the smaller seed
U=[C_V(O₂(LA)),L] and its literal faithful quotient LA/C_LA(U). Applying
the complete B.5.1 implication there and comparing every source alternative
gives the five local actions. The preliminary assembly proves U=[V,L],
the supplements and offender placement in the non-IV cases, and retains
the actual LA-action on the natural SL₃ seed in case (IV).

`preliminary_of_source` applies to every moved component and every literal
`MovedSection`. It assumes neither a preparation nor a local classification.
`naturalClosureSetup_of_source` supplies the universal preliminary conclusion
and component normality to the actual natural-enlargement consumer. It makes
no assertion that the seed already equals the full moved space.

Exactly three universal earlier-source implications remain explicit:
* `Preparation.ComponentInput`: complete B.5.5, produced by
  `qt-b05-quotient-components`;
* `ProjectiveLine.QuasisimpleClassificationInput`: all six B.5.1 clauses,
  with the full corrected B.4.2 alternatives, produced by `qt-b05-quasisimple`;
* `ThreeCovers.CentralExtension.EarlierB48Two`: B.4.8(2), with its original
  faithful indecomposable four-dimensional action and natural central quotient,
  produced by `qt-b-04-natural-extensions` / `qt-b-04`.

Their final discharge belongs to `qt-b05-general-classification`. No separate
B.5.2, A.1.31 or I.1.6 implication is assumed here: preparation and comparison
use the checked rank, cohomology, B.1.5 restriction and B.7.2 invariance proofs.
The final case-(IV) enlargement belongs to `qt-b05-component-natural-closure`,
and B.5.9–10 assembly to `qt-b05-induction-component-reduction`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed pp.107–108, stopping before the final natural-SL₃ enlargement.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The preliminary component classification of B.5.9. All faithful-quotient
preparation and local comparison premises are discharged from the source
setup and the three complete earlier implications. -/
theorem preliminary_of_source
    (h5 : Preparation.ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAF : A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) :
    PreliminaryConclusion ρ A L s :=
  preliminary_of_prepared_source_classification ρ h48 h1 hyp hA h3 hL hLA s
    (Preparation.prepared_of_source ρ h5 hyp hA hAF h3 hL hLA)

/-- Supply the actual natural-enlargement consumer, including every moved
component rather than only the initially chosen one. Component normality
comes from full B.5.5; the universal preliminary field is the theorem above. -/
theorem naturalClosureSetup_of_source
    (h5 : Preparation.ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (h48 : ThreeCovers.CentralExtension.EarlierB48Two.{u,v})
    (hyp : FFHypothesis K ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAF : A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1) :
    NaturalClosure.Setup ρ K A where
  hypothesis := hyp
  minimal := hA
  centralizes_fitting := hAF
  component_normal := (h5 G V ρ hyp).normal
  component_three_rank := h3
  preliminary M hM hMA s :=
    preliminary_of_source ρ h5 h1 h48 hyp (L := M) hA hAF h3 hM hMA s

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
