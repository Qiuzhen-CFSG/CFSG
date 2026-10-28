module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331.WholeOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.GuardedSource318
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source

/-!
# The original maximal counterexample under the genuine standing guard

For any nonquasisimple faithful local component, the guarded 3.1.8 theorem
bounds every actual chosen-module orbit. All A/C, component structure,
normality and A.4.10 source inputs in the maximal-overgroup construction
are already proved. The resulting maximal component retains its original
canonical radical and full normalizer identity. No unguarded Chapter 3
implication is formed or assumed.

Source: Aschbacher--Smith 13.1.4 and the setup of 13.1.7, pp.867--868.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Choose the actual maximal 13.1.7 counterexample from the guarded earlier
source theorem and the original standing two-maximal-local condition. -/
theorem Hypothesis1311.maximal_counterexample_of_guarded_source318
    (h : Hypothesis1311 T) (h318 : Chapter3.GuardedSourceTheorem318One G)
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
        normalizer (K : Set G) = normalizer (XiP p L₀ : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  exact h.exists_maximal_counterexample_of_orbit_bound h36
    (fun _ _ _ hG hO _ hC => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hG hO hC)
    ChapterA.Section04.SourceChains.adequate_source
    (fun _ _ hK D => D.orbit_cubicRatio_le_of_guarded_source318 hK.toHypothesis1221 h318 hout) hL

end CFSG.Quasithin.Chapter13.Section01
