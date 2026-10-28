module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Comparison
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.CyclicCenter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications
/-!
# Actual starred-family placement from the earlier 13.3.2 list

Two-perfectness puts any prospective containing residual in the component
orbit. The proved A.4.10 and 1.3.9(2) make that component faithful; 13.3.2(2)
then fixes its orbit. The normal alternative of the complete intrinsic
embedding theorem contradicts the noncyclic odd complement and cyclic
quotient center. In the other alternatives, apply the same faithful-family
transfer to the detected component, then use the proved five-model comparison.
The corrected adequate embedding theorem retains Held throughout.

`Source1332OneTwo` is precisely the earlier list and T-normality implication;
it is an explicit source premise, not a claimed proof of 13.3.2. In particular
there is no starred-placement, embedding, model-disjointness or A.4.10 premise.

Source: Aschbacher--Smith, Lemmas 1.3.4,1.3.9(2),13.3.2(1--2), and the
starred-family step in 13.3.14(d), printed pp.509--514,884--885,892.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter1 Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]
@[expose] def Source1332OneTwo (T : Sylow 2 G) : Prop :=
  ∀ K ∈ MainForward.faithfulLocalComponents T,
    (T : Subgroup G) ≤ normalizer K ∧ MidSizeModel (XiQuotient K)

private theorem local_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple H := by
  let N := normalizer (H.pCoreIn 2 : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨H.pCoreIn 2,hH,isPGroup_pCoreIn 2 H,rfl⟩
  have hs := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hs.stronglyQuasithin.of_injective (subgroupOfEquivOfLe hHN).symm.toMonoidHom
    (subgroupOfEquivOfLe hHN).symm.injective,
    hs.isKGroup.of_injective (subgroupOfEquivOfLe hHN).symm.toMonoidHom
      (subgroupOfEquivOfLe hHN).symm.injective⟩

theorem source_XiF_subset_XiStarF
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) : XiF G (T : Subgroup G) ⊆ XiStarF G (T : Subgroup G) := by
  intro X hX
  refine ⟨hX,hX.1,?_⟩
  intro B hB hQB hXB
  have hXorbit := le_componentOrbit_of_twoPerfect hX.1.perfect T.isPGroup'
    (le_sup_left.trans hXB)
  have hfB := (Terminal.lemma_1_3_9_two_source hG T hX hB hXorbit).2
  obtain ⟨hTB,hmB⟩ := h1332 B hfB
  have horbit : componentOrbit B (T : Subgroup G) = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB)
      (le_componentOrbit B _)
  have hXBle : X ≤ B := horbit ▸ hXorbit
  obtain ⟨p,hp,ho,hq⟩ := hX.1.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let d := localInput_of_mem_Xi hX.1 hB.2.1 hXB ho hq (default : Sylow p X)
  rcases d.adequate_knownSimple (local_sqtk hG hB.2.2) hB.2.1 with hn | ⟨L,hL,hQL,hXL,ha⟩
  · let : IsQuasisimple (XiQuotient B) := hQB
    let : IsCyclic (center (XiQuotient B)) := hmB.center_cyclic
    exact d.not_normal_in_cyclic_center_component hX.1 hXBle le_sup_left hn
  · have hLL := (lemma_1_2_6 T ⟨hB.2.2,show (T : Subgroup G) ≤ B ⊔ T from le_sup_right⟩).1 hL
    have hfL := (Terminal.lemma_1_3_9_two_source hG T hX hLL.2 hXL).2
    obtain ⟨hTL,hmL⟩ := h1332 L hfL
    exact not_adequate_alternatives_of_midSize hp ho hTL hmL ha
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
