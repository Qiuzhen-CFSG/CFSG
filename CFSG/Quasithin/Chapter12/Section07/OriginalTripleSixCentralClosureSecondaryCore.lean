module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryMarked

/-!
# The original whole core equals the chosen hexacode module

In the contrary branch the actual whole secondary module has the original
natural point marking. Its actual W-eight image is the duad two-core under
the retained even relabeling, so it has a nonzero second displacement.
This contradicts the literal quadratic W-action proved from the original
almost-special central closure. Therefore O2(KT)=U.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual marked eight-actor contradiction rules out a larger core.
All genuine original source inputs are retained; no block recognition is assumed. -/
theorem original_tripleSix_central_closure_secondary_core_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 = U := by
  by_contra hQ
  obtain ⟨hr,hj,hMU,f,hf,hfk,hchart,hπ,hker,hq,hqker,σ,⟨r,hrW⟩,hquad,⟨e⟩,hfaith,
      hfixed,hm,hirr,hdim,hmodels,hσ,he,hbound,hcases⟩ :=
    original_tripleSix_central_closure_secondary_marked_product
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter hQ
  let := hr.elementary
  let := hj.elementary
  apply BinaryAlternatingSix.not_quadratic_of_equiv_firstNatural_of_conjugate_duadCore
    σ e _ r.val _ hquad
  rwa [map_map]

end CFSG.Quasithin.Chapter12.Section07
