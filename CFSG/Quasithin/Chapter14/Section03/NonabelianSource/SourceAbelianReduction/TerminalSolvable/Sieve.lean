module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Noncontainment

/-!
# Applying the proved component exclusions to the actual terminal lift

Perfectness and relative normality supply the noncontainment in M needed
by the G₂(2)′ and A₇ exclusions. The M₂₂ exclusions need only the original
conjugate-span equality. Hence the four actual two-core quotient rows are
impossible, leaving only the dotted A₅, A₆ and L₂(8) rows.

Catalogue construction and elimination of those remaining rows are separate
source obligations. Source: Aschbacher--Smith 14.3.6 and 14.3.15, pp.991--994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open EmptyFamilySieve
variable {G : Type*} [Group G] [Finite G]

/-- The source sieve on an actual lifted terminal component; no outside-M
assumption is added to the component contract. -/
theorem source_excluded_quotient_row_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G) (K : Subgroup G)
    (hK : ComponentLift F g K)
    (horbit : K = conjugateSpanBy K (T : Subgroup G))
    (hrow : ExcludedQuotientRow K) : False := by
  have hout := hK.not_le hM.1.2 e
  unfold ExcludedQuotientRow at hrow
  rcases hrow with ⟨eK⟩ | ⟨eK⟩ | ⟨eK⟩ | ⟨eK⟩
  · exact source_orbit_derived_g2_false hG T hempty hM hu hmany hcard e hnot
      K hK.local_component horbit hout (Classical.choice eK)
  · exact source_orbit_a7_false hG T hempty hM hu hmany hcard e hnot
      K hK.local_component horbit hout (Classical.choice eK)
  · exact source_orbit_m22_false hG T hempty hM hu hmany hcard e hnot
      K hK.local_component horbit (Classical.choice eK)
  · exact source_orbit_triple_m22_false hG T hempty hM hu hmany hcard e hnot
      K hK.local_component horbit (Classical.choice eK)

/-- The literal terminal catalogue reduces to its two still-unproved source
branches. The first includes the exchanged A₅ component orbit. -/
theorem source_component_cases_reduce
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G) (K : Subgroup G)
    (hK : ComponentLift F g K) (hcases : ComponentCases F K) :
    SmallImageRow F K ∨ EightImageRow F K := by
  unfold ComponentCases at hcases
  rcases hcases with ⟨horbit,hrow⟩ | hremaining
  · exact (source_excluded_quotient_row_false hG T hempty hM hu hmany hcard e hnot
      F g K hK horbit hrow).elim
  · exact hremaining

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
