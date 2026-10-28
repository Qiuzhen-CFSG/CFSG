module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.SourceComplete

/-!
# The source maximal counterexample with the orbit bound discharged

The simple QTKE field of Hypothesis 13.1.1 proves guarded Theorem 3.1.8.
Its application to each original chosen-module orbit supplies the maximal
counterexample construction, including the canonical odd radical and its
full normalizer identity. Only the actual standing outside-local condition
remains as an ambient geometric hypothesis.

Source: Aschbacher--Smith 13.1.4 and the setup of 13.1.7, pp.867--868.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual maximal counterexample, with no earlier cubic-bound callback. -/
theorem Hypothesis1311.maximal_counterexample_source
    (h : Hypothesis1311 T)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Chapter3.HasMaximalOutside T M)
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
  h.maximal_counterexample_of_guarded_source318
    (Chapter3.source_guardedTheorem318One h.simpleQTKE) hout hL

end CFSG.Quasithin.Chapter13.Section01
