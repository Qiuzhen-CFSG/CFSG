module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Selection
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
/-!
# The 13.1 maximal counterexample inside the original 13.3.1 setup

The later source hypotheses imply the original 13.1.1 exclusions. If their
selected faithful component has nonquasisimple two-core quotient, the actual
13.1 counterexample construction produces a maximal faithful overgroup and
its unique maximal two-local normalizer. The complete known-simple A/C
source and covering catalogue discharge A.3.6 here. The remaining earlier
inputs are the specified A.3.8 normality clause, A.4.10 and the genuine
whole-orbit cubic-ratio bound; the final 13.1.7 contradiction is not assumed.

Source: Aschbacher--Smith, 13.1.4 and the first reduction in13.3.2,
printed pp.867--868 and884.
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
theorem Hypothesis1331.maximal_counterexample_of_orbit_bound
    (h : Hypothesis1331 T L₀)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
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
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  exact h.hypothesis1311.exists_maximal_counterexample_of_orbit_bound
    h36 hA38 hA410 hbound ⟨h.local_component,hn⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
