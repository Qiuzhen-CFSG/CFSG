module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Pushing
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow

/-!
# Assembly of the half-Sylow uniqueness argument

The normalizer bound of 10.2.5 gives the prescribed Sylow subgroup in a
competing maximal two-local. The proved containment reduction constructs
the exact normal containing pair inspected in 10.2.6. Excluding that pair
establishes uniqueness for L₀N_T(L), independently of the chosen seed.

The two source inputs remain explicit until their independent producers
prove them. This module does not assert unconditional 10.2.6. Its output
has precisely the `HalfSylowUniqueAt` type consumed by the point-control
assembly; the normalizer consumer below also applies it on the literal
component and moved module.
Source: Aschbacher--Smith, 10.2.5--6, printed pp.747--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The normalizer and containing-component arguments together discharge
the exact `hhalf` input of `source_nonnormalPointControl_of_sourceSteps`. -/
theorem halfSylowUniqueAt_of_sourceSteps
    (hN : StabilizerNormalizerAt T) (hpair : ContainingPairExclusionAt T) :
    HalfSylowUniqueAt T := by
  intro hmany L D hn hna H hH hhalf
  by_contra hne
  obtain ⟨t,K₁,K₂,hC⟩ := exists_containingPair D (hN hmany L D hn hna) hn hH hne hhalf
  exact hpair hmany L D hn hna H t K₁ K₂ hC

/-- The two literal normalizer consequences used by point control, with
their half-Sylow premise discharged by the preceding conditional assembly. -/
theorem normalizers_le_of_sourceSteps
    (hN : StabilizerNormalizerAt T) (hpair : ContainingPairExclusionAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    normalizer (L : Set G) ≤ D.maximalLocal ∧
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hhalf := halfSylowUniqueAt_of_sourceSteps hN hpair hmany L D hn hna
  exact ⟨component_normalizer_le_of_halfSylowUnique D hn hhalf,
    moved_normalizer_le_of_halfSylowUnique D hn hhalf⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
