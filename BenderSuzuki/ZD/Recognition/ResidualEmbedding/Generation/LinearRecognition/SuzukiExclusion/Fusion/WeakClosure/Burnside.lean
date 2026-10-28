module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces
public import Theory.GroupTheory.AbelianWeakClosureFusion

/-!
# Burnside fusion in the actual Suzuki quotient

The image of an ambient Sylow two-subgroup is Sylow in M/M°. When this
image is abelian, Burnside fusion makes invariance of the image of U under
its normalizer sufficient for weak closure. This uses the actual maps
S → M → M/M° and does not require a separate abstract quotient marking.

Source: GLS4, Chapter 2, Lemma 14.9, the application of Burnside's fusion
lemma after Lemma 14.7(b); `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFchapter1section1

private theorem weaklyClosed_of_abelian_sylow_normalizer
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    [IsMulCommutative (P : Subgroup H)] (U : Subgroup H)
    (hUP : U ≤ (P : Subgroup H))
    (hn : normalizer (P : Set H) ≤ normalizer (U : Set H)) :
    External.WeaklyClosedIn (P : Subgroup H) U := by
  have hPweak : ∀ a : H, (P : Subgroup H).conjBy a ≤ (P : Subgroup H) →
      (P : Subgroup H).conjBy a = (P : Subgroup H) := by
    intro a ha
    exact eq_of_le_of_card_ge ha
      (le_of_eq (card_map_of_injective (MulAut.conj a).injective).symm)
  refine ⟨hUP, ?_⟩
  intro a ha
  apply eq_of_le_of_card_ge ?_
    (le_of_eq (card_map_of_injective (MulAut.conj a⁻¹).injective).symm)
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨n, hnP, hnu⟩ := P.normalizer_fuses_of_abelian_weakly_closed
    (P : Subgroup H) le_rfl hPweak (hUP hu) (ha (mem_map_of_mem _ hu))
      (isConj_iff.mpr ⟨a⁻¹, rfl⟩)
  have hmem := mem_map_of_mem (MulAut.conj n).toMonoidHom hu
  have heq : U.map (MulAut.conj n).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (hn hnP)
  rw [heq] at hmem
  change MulAut.conj n u ∈ U at hmem
  rwa [hnu] at hmem

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Burnside fusion for the literal quotient images of S and U. -/
public theorem quotientFusion_of_elementary_normalizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (he : ElementaryQuotient d g) (hn : QuotientNormalizerInvariant d g) :
    QuotientFusion d g := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  obtain ⟨V, hV⟩ := s.S_sylow
  let W := V.subtype (show (V : Subgroup G) ≤ M by rw [hV]; exact g.S_le_M)
  let P := W.mapSurjective (QuotientGroup.mk'_surjective (A.subgroupOf M))
  have hP : (P : Subgroup (M ⧸ A.subgroupOf M)) = (g.S.subgroupOf M).map pi := by
    simp only [P, Sylow.coe_mapSurjective, W, Sylow.coe_subtype, hV, pi]
  have he' : IsElementaryAbelian 2 (P : Subgroup (M ⧸ A.subgroupOf M)) := by
    rw [hP]
    exact he
  let := he'
  change External.WeaklyClosedIn ((g.S.subgroupOf M).map pi) ((g.U.subgroupOf M).map pi)
  rw [← hP]
  apply weaklyClosed_of_abelian_sylow_normalizer P ((g.U.subgroupOf M).map pi)
  · rw [hP]
    exact map_mono (subgroupOf_mono M g.U_le_S)
  · change normalizer ((g.S.subgroupOf M).map pi : Set (M ⧸ A.subgroupOf M)) ≤
      normalizer ((g.U.subgroupOf M).map pi : Set (M ⧸ A.subgroupOf M)) at hn
    change normalizer ((P : Subgroup (M ⧸ A.subgroupOf M)) : Set (M ⧸ A.subgroupOf M)) ≤ _
    rw [hP]
    exact hn

end BenderSuzuki.ZD.SuzukiExclusion
