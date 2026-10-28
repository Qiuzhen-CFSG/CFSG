module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.SourceComplete
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# Original maximal counterexamples in the multiple-overgroup branch

The Main Theorem's actual multiple-overgroup hypothesis supplies an outside
maximal two-local for every selected local. The proved guarded 3.1.8 source
then constructs the maximal nonquasisimple faithful overgroup with its
canonical odd radical and unique full normalizer. The second theorem applies
this construction directly to Hypothesis 13.3.1, with no separate A.3.8,
A.4.10, orbit bound or standing-guard premise. The later 13.1.7 elimination
of this counterexample remains a distinct source argument.

Source: Aschbacher--Smith 13.1.4 and the opening of 13.3.2,
printed pp.867--868 and 884, under the standing assumption after 2.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original multiple-overgroup hypothesis supplies every standing guard
in the maximal-counterexample construction. -/
theorem Hypothesis1311.maximal_counterexample_of_many
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      K ∈ nonquasisimpleFaithful T ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      (∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (K : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        XiP p L₀ = XiP p K ∧
        normalizer (K : Set G) = normalizer (XiP p L₀ : Set G) :=
  h.maximal_counterexample_source (Chapter3.hasMaximalOutside_of_many T hmany) hL

end CFSG.Quasithin.Chapter13.Section01

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal nonquasisimple branch of 13.3.2 admits its maximal source
counterexample, with all preceding cubic and catalogue inputs discharged. -/
theorem Hypothesis1331.maximal_counterexample_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      K ∈ nonquasisimpleFaithful T ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      (∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (K : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧ XiP p L₀ ≠ ⊥ ∧
        XiP p L₀ = XiP p K ∧
        normalizer (K : Set G) = normalizer (XiP p L₀ : Set G) :=
  h.hypothesis1311.maximal_counterexample_of_many hmany ⟨h.local_component, hn⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
