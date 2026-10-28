module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Assembly

/-!
# Applying the faithful seed preparation to the preliminary alternatives

The original source hypotheses now supply `Prepared` for the literal quotient
LA/C_LA(U). This application discharges that argument of
`preliminary_of_local_alternative`. The independent representation comparison
still supplies `LocalAlternative`; its assembly owner is
qt-b05-component-preliminary-actions. The full universal B.5.5 implication
is produced by qt-b05-quotient-components, with final discharge by
qt-b05-general-classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed pp.107–108.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The actual preliminary-classification consumer, with every faithful seed
preparation premise discharged from the source setup and the full B.5.5 input. -/
theorem preliminary_of_source_local_alternative
    (earlier : ComponentInput.{u,v} K) (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAF : A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L)
    (cases : LocalAlternative ρ hLA) : PreliminaryConclusion ρ A L s :=
  preliminary_of_local_alternative ρ hyp hA hL hLA s
    (prepared_of_source ρ earlier hyp hA hAF h3 hL hLA) cases

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
