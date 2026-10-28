module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.JankoFourContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.RudvalisContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Source

/-!
# Complete containing-pair exclusion for the literal half-Sylow join

The full Theorem C sieve leaves an actual strict J4 containing quotient.
Its order excludes a Suzuki original factor and excludes both original
factors in the same component. The checked cubic-rank contradiction closes
that final row. All containing-model, distinctness and relative-normality
premises are discharged on the original ordered pair and exchanger.

Only the independent source module choice is required for this exclusion.
The normalizer in source 10.2.5 is still required by the uniqueness consumer;
its zero-kernel binary-three case remains with qt-d-10-nona5-half-sylow-unique.
The ultimate discharge of ModuleChoiceAt and unconditional point-control
assembly belong to qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.6, pp.748--749, using A.3.12 and C.2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- All literal containing-pair branches are excluded from the source choice. -/
theorem containingPairExclusionAt_of_moduleChoice
    (hchoice : Selection.ModuleChoiceAt T) : ContainingPairExclusionAt T := by
  intro hmany L D hn hna H t K₁ K₂ C
  rcases C.exists_strict_jankoFour_quotient hchoice hmany hn hna with ⟨_,he⟩ | ⟨_,he⟩
  · exact C.impossible_of_first_jankoFour_quotient hchoice hmany hn hna he
  · exact C.impossible_of_second_jankoFour_quotient hchoice hmany hn hna he

/-- Apply the complete containing-component argument to the original uniqueness contract. -/
theorem halfSylowUniqueAt_of_moduleChoice_and_normalizer
    (hchoice : Selection.ModuleChoiceAt T) (hN : StabilizerNormalizerAt T) :
    HalfSylowUniqueAt T :=
  halfSylowUniqueAt_of_sourceSteps hN (containingPairExclusionAt_of_moduleChoice hchoice)

/-- The literal point-control normalizers with all containing-model premises discharged. -/
theorem normalizers_le_of_moduleChoice_and_normalizer
    (hchoice : Selection.ModuleChoiceAt T) (hN : StabilizerNormalizerAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    normalizer (L : Set G) ≤ D.maximalLocal ∧
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal :=
  normalizers_le_of_sourceSteps hN (containingPairExclusionAt_of_moduleChoice hchoice)
    hmany D hn hna

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
