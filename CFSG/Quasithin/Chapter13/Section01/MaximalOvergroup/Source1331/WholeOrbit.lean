module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331.ComponentNormality
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications
/-!
# Source13.1 counterexample setup with the faithful-chain theorem discharged

The original A.4.10 is now proved and supplies the faithful-chain input.
All A/C, component-structure and normality inputs are likewise discharged.
Only the genuine whole-orbit3.1.8/3.2.5 bound remains explicit in this
maximal-overgroup construction. This does not assert the later13.1.7
contradiction or the full seven-row12.2 classification.

Source: Aschbacher--Smith13.1.4(2) and13.3.2, pp.867--868 and884.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02 Chapter13.Section01
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal source counterexample, with no chosen-module or quotient-model
certificate among its inputs. Its later elimination is the remaining13.1.7. -/
theorem Hypothesis1331.maximal_counterexample_from_whole_orbit
    (h : Hypothesis1331 T L₀)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
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
  h.maximal_counterexample_of_source_orbit_bound
    ChapterA.Section04.SourceChains.adequate_source hbound hn

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource

namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe v
variable {G : Type v} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original13.1.4(2), with all component-structure and normality inputs
proved; the earlier faithful-chain and whole-orbit theorems remain explicit. -/
theorem Hypothesis1311.radical_normalizer_unique_from_whole_orbit
    (h : Hypothesis1311 T)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    IsMaximalTwoLocal (normalizer (XiP p L₀ : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (XiP p L₀ : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (XiP p L₀ : Set G) :=
  h.radical_normalizer_unique_source ChapterA.Section04.SourceChains.adequate_source
    hbound hL ho hd

end CFSG.Quasithin.Chapter13.Section01
