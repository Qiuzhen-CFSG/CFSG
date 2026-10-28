module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced

/-!
# The DGS reduced pair in the original tensor configuration

Under the zero-core assumption in the proof of 9.3.3, both original Borels
normalize the common two-group. DGS (6.1) can therefore be applied in its
A5 row: replacing the two local factors by their joins with the same S
produces another genuine F.1.1 pair. Its full overlap, both parabolics and
completion are unchanged. The quotient maps below are induced by the
original factor inclusions; their kernels and surjectivity are proved.

This is the entrance to the reduced DGS argument. It does not identify the
original local cores with the enlarged cores, and therefore does not yet
prove the nonzero-core conclusion of 9.3.3.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs, Part II,
(6.1), pp.118--119; Aschbacher--Smith 9.3.3, p.733, and F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 SourceOldResidualOvergroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The literal reduced DGS pair, with the original completion and full
Borel retained, under the source's temporary zero-core assumption. -/
theorem old_residual_core_zero_reduced_rank_two_source
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    let P : Fin 2 → Subgroup G := ![L, (pResidual 2 H).map H.subtype]
    let S := commonTwo T L
    ChapterF.Source.HypothesisF11 (fun i => P i ⊔ S) S ∧
    IsQuasithin (ChapterF.Source.generated (fun i => P i ⊔ S) S) ∧
    ChapterF.Source.commonBorel (fun i => P i ⊔ S) S = ChapterF.Source.commonBorel P S ∧
    ChapterF.Source.twoCore (ChapterF.Source.commonBorel P S) = S ∧
    ∀ i,
      ChapterF.Source.parabolic (fun j => P j ⊔ S) S i = ChapterF.Source.parabolic P S i ∧
      ChapterF.Source.twoCore (P i ⊔ S) =
        ChapterF.Source.twoCore (ChapterF.Source.parabolic P S i) ∧
      Nonempty (((P i ⊔ S : Subgroup G) ⧸ pCore 2 (P i ⊔ S : Subgroup G)) ≃*
        alternatingGroup (Fin 5)) ∧
      (ChapterF.Source.HypothesisF11.localJoinQuotientMap P S i).ker = pCore 2 (P i) ∧
      Function.Surjective (ChapterF.Source.HypothesisF11.localJoinQuotientMap P S i) := by
  obtain ⟨hf, hqt, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  dsimp only
  refine ⟨hf.a5_localJoin_hypothesis hn hq, ?_, hf.localJoin_commonBorel_eq hn,
    hf.commonBorel_twoCore_eq hn, ?_⟩
  · rwa [ChapterF.Source.HypothesisF11.localJoin_generated_eq]
  · intro i
    obtain ⟨ei⟩ := hq i
    exact ⟨hf.localJoin_parabolic_eq hn i, hf.localJoin_twoCore_eq_parabolic hn i,
      ⟨(hf.a5_localJoinQuotientEquiv hn i ei).symm.trans ei⟩,
      hf.localJoinQuotientMap_ker hn i, hf.a5_localJoinQuotientMap_surjective hn i ei⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
