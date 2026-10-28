module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Centralizer
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Restriction
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Source
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingSingleBlock
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# The moved alternating single-block index calculation

Retain the Thompson movement equation from E.6.7. Together with relative
normality and the original Sylow intersection it constructs the actual
rank-one/A₃ or alternating-five C.5.4 setup. C.1.11 identifies the module
centralizer, and C.5.5 then constructs a noncommuting conjugate. Applying the
proved family theorem C.5.7 gives index two for the literal block normalizer.
No Baumann or conjugate-family callback is assumed.

The L₃ hyperplane consumer supplies the movement equation from its own
E.6.7 decomposition. This theorem does not assert the unrestricted generic
SingleBlockIndexInput contract.

Source: Aschbacher–Smith C.5.4–7, printed pp.155–160, and E.6.14, p.251.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex
open ChapterC ChapterC.Section05 ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- The pointwise C.5.7 index from the original block movement equation. -/
theorem index_of_moved_alternating (h : Configuration K A H R L)
    (hm : L = ⁅L,Stellmacher.elementaryAbelianMaxJ R⁆)
    (ht : IsAlternatingBlock L 3 ∨ IsAlternatingBlock L 5) :
    (localNormalizer A L).relIndex A = 2 := by
  have hRH : R ≤ H := h.join_eq ▸ le_sup_right
  have hLH : L ≤ H := h.join_eq ▸ le_sup_left
  have hR := (Chapter1.isSylowIn_iff.mp h.sylow).1
  have hRL : R ≤ normalizer (L : Set G) := hRH.trans h.normalizes_L
  have hBL : ChapterB.baumann R ≤ normalizer (L : Set G) := inf_le_left.trans hRL
  have hLn : (L.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLH).mpr h.normalizes_L
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    h.sylow hLH hLn.isSubnormal
  have hc := Baumann.singleBlockCentralizerInput H R L h.characteristicTwo
    h.sylow h.normalizes_L h.join_eq h.block
  have hcent : R ⊓ centralizer (U L : Set G) ≤ pCoreIn 2 H := by
    rw [← hc]
    exact inf_le_inf_right _ hRH
  have hmax : IsCoatom ((normalizer (L : Set G)).subgroupOf A) := by
    apply CovBy.isCoatom
    apply (covBy_map_subtype_iff A _ _).mp
    rw [subgroupOf_map_subtype, ←MonoidHom.range_eq_map,range_subtype,inf_comm]
    exact h.maximal
  have hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      A ≤ normalizer (W : Set G) → W = ⊥ := by
    intro W hWR hHW hAW
    by_contra hne
    apply h.no_common
    refine ⟨W,hWR,hne,Chapter3.normalIn_iff_le_normalizer.mpr ?_⟩
    rw [Chapter3.generated_eq_sup]
    exact ⟨hWR.trans (h.le_A.trans le_sup_left),sup_le hAW hHW⟩
  rcases ht with h3 | h5
  · obtain ⟨F,hF,⟨s⟩⟩ := exists_rankOne_setup R L hR (Or.inr h3) hm hBL P hP
    let _ := hF
    have hb : BaumannStructure H R L := ⟨s.module_le,hcent,s.core⟩
    obtain ⟨x,hx,hnc⟩ := exists_noncommuting_conjugate h hb
    have hi := s.source_C57 H A R h.le_A h.normalizes_R hRL h.join_eq.symm
      hno hmax x⁻¹ (A.inv_mem hx)
        (by simpa only [inv_inv,U,ConjugateSource.RankOne.U] using hnc)
    simpa only [localNormalizer,inf_relIndex_left] using hi.2.1
  · obtain ⟨s⟩ := exists_alternatingPairSetup R L ⊥ hR h5 hm hBL P hP bot_le
      (fun r hr => Or.inl (mem_normalizer_iff_map_conj_eq.mp (hRL hr)))
    have hb : BaumannStructure H R L := ⟨s.module_le,hcent,s.core⟩
    obtain ⟨x,hx,hnc⟩ := exists_noncommuting_conjugate h hb
    have hi := s.source_C57 hRL H A R h.le_A h.normalizes_R hRL h.join_eq.symm
      hno hmax x⁻¹ (A.inv_mem hx)
        (by simpa only [inv_inv,U,ConjugateSource.sourceModule] using hnc)
    simpa only [localNormalizer,inf_relIndex_left] using hi.2.1

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex
