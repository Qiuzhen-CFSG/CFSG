module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331.WholeOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
/-!
# The canonical 3.1.8 input in the original 13.1 argument

The whole-orbit bound is now obtained from the literal earlier source theorem
3.1.8(1), using the original chosen module and centralizer quotient. All other
inputs to the radical normalizer and maximal-counterexample construction are
proved. The universal 3.1.8 theorem remains with its earlier source producer;
these statements do not assert the subsequent 13.1.7 contradiction.

Source: Aschbacher--Smith, 13.1.4(2) and the setup of 13.1.7, pp.867--868.
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
theorem Hypothesis1331.maximal_counterexample_of_source318
    (h : Hypothesis1331 T L₀)
    (h318 : Chapter3.SourceTheorem318One G)
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
  h.maximal_counterexample_from_whole_orbit
    (fun _ _ hK D => D.orbit_cubicRatio_le_of_source318 hK.toHypothesis1221 h318) hn

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource

namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe v
variable {G : Type v} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original 13.1.4(2) from the named earlier theorem 3.1.8(1). -/
theorem Hypothesis1311.radical_normalizer_unique_of_source318
    (h : Hypothesis1311 T)
    (h318 : Chapter3.SourceTheorem318One G)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    IsMaximalTwoLocal (normalizer (XiP p L₀ : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (XiP p L₀ : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (XiP p L₀ : Set G) :=
  h.radical_normalizer_unique_from_whole_orbit
    (fun _ _ hK D => D.orbit_cubicRatio_le_of_source318 hK.toHypothesis1221 h318) hL ho hd

end CFSG.Quasithin.Chapter13.Section01
