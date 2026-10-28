module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceSeedBound
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple
/-!
# The original E.6.3 route with full earlier sources supplied

All uses of A.3.12 in the preceding boundary occurred only through the genuine
common-normal theorem. The completed known-simple C.5/3.1.1 source now supplies
that exact theorem, without an unrestricted embedding premise. The original
local containment, residual normality, E.6.7 family, I.3 lifting, regular section
and cyclic factor-seed sources supply the remaining earlier steps.

The original minimum ranges over the full globalR domain. The three explicit
remaining model producers are E.6.8's adequate sieve, E.6.18's seven exclusion,
and recognition of the actual further component in E.6.23. No earlier theorem,
common-normal conclusion, factor seed or selected subgroup is assumed separately.
Source: Aschbacher–Smith E.6.3,E.6.13,E.6.18–25, pp.245,250,252–256.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

namespace FrobeniusReduction
open Components Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open InvariantSubspaces.BlockSelection

theorem lower_bound_knownSimple_of_remaining_models [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  have h311 := InvariantSubspaces.source_commonNormalInput_knownSimple T
  have ho := source_oddCoreFree h (Or.inr hm) h311 h18 h68
  have h23 := source_rank_gt_one_of_quotientRecognition h hm h311 h18 h68 hquot
  have h67 := e67Input_knownSimple h
  have hsieve := fun A hA X hX => (h68 A hA X hX).borel_symplectic_or_rank_one
  apply lower_bound_of_earlier_sources h hm h311 source_localContainment
    (source_residualNormalization KnownSimple.IsKnownSimple) ho h67 ?_ h23 ?_
    (fun _ hi => CFSG.Quasithin.RegularCyclicNormalClosure.exists_factorSeed_of_input hi)
  · intro A hA X hX
    rcases hsieve A hA X hX with hb | hs | hr
    · exact Or.inl hb
    · exact Or.inr (Or.inl hs)
    · exact (h23.ne' hr).elim
  · intro U hU hmin hr
    exact minimalRegularSection_of_source_models h h67 hU hmin hr (hsieve U hU)
end FrobeniusReduction
end CFSG.Quasithin.ChapterE.Section06
