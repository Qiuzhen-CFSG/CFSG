module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
/-!
# The original 13.3.1 counterexample with component normality discharged

The proved noncentral rank argument supplies the universal A.3.8
normal-or-quasisimple implication. Together with the completed A/C and
A.3.6 sources, it constructs the original maximal counterexample normalizer.
Only the genuine earlier A.4.10 and whole-orbit cubic-ratio bound remain
explicit here. The later contradiction eliminating the counterexample is
still the separate 13.1.7 argument.

Source: Aschbacher--Smith 13.1.4 and13.3.2, pp.867--868 and884.
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
theorem Hypothesis1331.maximal_counterexample_of_source_orbit_bound
    (h : Hypothesis1331 T L₀)
    (hA410 : A410EarlierResult G)
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
        normalizer (K : Set G) = normalizer (XiP p L₀ : Set G) := by
  exact h.maximal_counterexample_of_orbit_bound
    (fun _ _ _ hG hO _ hC => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hG hO hC)
    hA410 hbound hn

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource

namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe v
variable {G : Type v} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original13.1.4(2), with all component-structure and normality inputs
proved; the earlier faithful-chain and whole-orbit theorems remain explicit. -/
theorem Hypothesis1311.radical_normalizer_unique_source
    (h : Hypothesis1311 T) (hA410 : A410EarlierResult G)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    IsMaximalTwoLocal (normalizer (XiP p L₀ : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (XiP p L₀ : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (XiP p L₀ : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  exact h.radical_normalizer_unique_of_orbit_bound h36
    (fun _ _ _ hG hO _ hC => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hG hO hC)
    hA410 hbound hL ho hd

end CFSG.Quasithin.Chapter13.Section01
