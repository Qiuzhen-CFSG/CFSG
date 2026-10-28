module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# The original nonnormal ordinary-component four-model source

Earlier universal A/C produce the full central-quotient catalogue. Perfect
central transfer proves that its original component is centerless, and distinct
commuting conjugates force every odd rank to be at most one. The complete
inspection leaves PSL₂ in even degree, Suzuki, odd-prime PSL₂ or J₁, with an
actual isomorphism on the original component. The existing orbit theorem adds
index two. No desired-output model hypothesis occurs in either source theorem.

Source: Aschbacher–Smith A.3.8(3), pp.45–46; used by Proposition 1.3.4, p.510.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
open Chapter1.Section02
universe u

/-- The genuine four-model conclusion for an original nonnormal ordinary component. -/
theorem nonnormal_component_model
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    {G : Type u} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal) :
    NonnormalCComponentModel B := by
  let : IsQuasisimple B := hB.2
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting hA hC hG B
    (Chapter1.XiEmbedding.component_isCComponent hB) hf).2
  have hz := FourModels.center_eq_bot_of_model
    (hG.stronglyQuasithin 3 (by decide) (by decide)) hcore B hB hnormal hm
  have hr := FourModels.odd_ranks_of_model hG.stronglyQuasithin hcore B hB hnormal hm
  let e : B ≃* B ⧸ center B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hrq : ∀ p : ℕ, p.Prime → Odd p → primeRank p (B ⧸ center B) ≤ 1 := by
    intro p hp ho
    rw [← primeRank_equiv p e]
    exact hr p hp ho
  exact (FourModels.model_of_odd_ranks hrq hm).of_mulEquiv e

/-- The orbit index and actual four-model conclusion, with original A/C only. -/
theorem nonnormal_component_index_and_model
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    {G : Type u} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal) :
    (normalizer (B : Set G)).index = 2 ∧ NonnormalCComponentModel B := by
  exact ⟨(Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    hG hcore (Chapter1.XiEmbedding.component_isCComponent hB)).resolve_left hnormal,
    nonnormal_component_model hA hC hG hcore B hB hnormal⟩

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
