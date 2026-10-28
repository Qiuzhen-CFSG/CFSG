module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingQuotient
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerOmegaSplitting
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSixQuadratic
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticNormalSubgroup

/-!
# The moved omega-module image in the alternating-six terminal argument

Mark the actual local residual X=O²(C_L(Ω₁Z(T))) as the first-four-letter A₄
in the natural six-letter quotient of LT. Original local invariance then
places the Sylow image in the complementary pair stabilizer. For the moving
odd element d, the elementary module Wᵈ is normalized by X and T. Since
U(L) ≤ W ≤ T, its quotient image acts quadratically on the actual block
module. The six-letter calculation forces that image into ⟨(4,5)⟩, and
movement outside O₂(LT) makes the image equal to this subgroup.

The final application constructs d and the full local marking, then invokes
the invariant-cubic terminal contradiction. The only additional premise is
the displayed image of the literal local residual in these coordinates.
The final variant uses the source-module splitting to express this residual
as O²(C_L(C_U(T))), leaving only the intrinsic module calculation.
Constructing that image and completing the other block rows remain with
`qt-d-12216-normalizer-block-centralizer`. The omega-generated module W,
the block layer U(L), and the chosen Chapter 12 module V remain distinct.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 3.3.25(2),
3.3.26 and the opening paragraph of 3.3.31, printed pp.599–602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original local invariance aligns the Sylow image with the pair
fixed by the marked local residual. -/
theorem alternating_six_sylow_image_le_of_residual_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) = K) :
    ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) ≤ H1 := by
  let H := L ⊔ (T : Subgroup G)
  let q := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
  have hTX : (T : Subgroup G) ≤ normalizer (blockLocalResidual T L : Set G) :=
    (T : Subgroup G).le_normalizer.trans
      (((blockLocalInvariance_of_alternating h D hfixed hb).1 (Or.inl hb)).1)
  have hn : ((T : Subgroup G).subgroupOf H).map q ≤
      normalizer (((blockLocalResidual T L).subgroupOf H).map q : Set S) :=
    (map_mono ((comap_mono hTX).trans (le_normalizer_comap H.subtype))).trans
      (le_normalizer_map q)
  rw [hX] at hn
  exact hn.trans normalizer_K_le_H1

/-- Movement and local normality determine the moved omega-module image;
there is no independent moved-image assumption. -/
theorem alternating_six_moved_image_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsAlternatingBlock L 6)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnormal : blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
      ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G))
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) = K)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) ≤ H1) :
    (((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
      (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) =
        zpowers swap45 := by
  let H := L ⊔ (T : Subgroup G)
  let A := (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom
  let q := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
  let E := (A.subgroupOf H).map q
  have hAT : A ≤ (T : Subgroup G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hd)]
    exact map_mono (blockOmegaModule_le_sylow h)
  have hAH : A ≤ H := hAT.trans le_sup_right
  let := blockOmegaModule_elementary h
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj d⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hEH : E ≤ H1 := (map_mono (comap_mono hAT)).trans hT
  have hXA : blockLocalResidual T L ≤ normalizer (A : Set G) := le_sup_left.trans hnormal
  have hnorm : K ≤ normalizer (E : Set S) := by
    rw [← hX]
    exact (map_mono ((comap_mono hXA).trans (le_normalizer_comap H.subtype))).trans
      (le_normalizer_map q)
  have hUA : (ChapterC.blockU L).map L.subtype ≤ normalizer (A : Set G) :=
    (blockU_le_blockOmegaModule h D hescape hb.2.1).trans
      ((blockOmegaModule_le_sylow h).trans (le_sup_right.trans hnormal))
  have hq := ChapterC.AlternatingSixBlockAction.joinPermutation_isQuadratic_of_normalizes
    D.sylow_normalizes_component m hρ A inferInstance hUA
  have hle : E ≤ zpowers swap45 := elementary_quadratic_normalized_K_le_swap45 E hE hEH hnorm hq
  have hne : E ≠ ⊥ := by
    intro he
    have hk : A.subgroupOf H ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp he
    rw [ChapterC.AlternatingSixBlockAction.joinPermutation_kernel
      D.sylow_normalizes_component m hρ hb.2.1] at hk
    apply hmove
    intro a ha
    exact hk (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha)
  obtain ⟨g,hg,hgne⟩ := E.bot_or_exists_ne_one.resolve_left hne
  have hgcases : g = 1 ∨ g = swap45 := by
    have hs : orderOf swap45 = 2 :=
      (show swap45.IsSwap from ⟨4,5,by decide,rfl⟩).orderOf
    have hm := mem_zpowers_iff_mem_range_orderOf.mp (hle hg)
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn2 : n < 2 := by simpa only [hs] using Finset.mem_range.mp hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  have he : g = swap45 := hgcases.resolve_left hgne
  exact le_antisymm hle (zpowers_le.mpr (he ▸ hg))

/-- The literal residual image determines the full local marking. The moved
image and the Sylow containment are proved from the original source inputs. -/
theorem alternating_six_local_marking_of_residual_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hmove : ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnormal : blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
      ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G))
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) = K) :
    Nonempty (AlternatingSixLocalMarking T L d) := by
  have hT := alternating_six_sylow_image_le_of_residual_image h D hfixed hb m hρ hX
  exact ⟨{
    quotient := ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ
    kernel := ChapterC.AlternatingSixBlockAction.joinPermutation_kernel
      D.sylow_normalizes_component m hρ hb.2.1
    local_image := hX
    sylow_image := hT
    moved_image := alternating_six_moved_image_eq h D hescape hb hd hmove hnormal m hρ hX hT }⟩

/-- Application to the original normalizer conclusion. Only construction of
coordinates for the actual local residual remains with the final owner
`qt-d-12216-normalizer-block-centralizer`; no moved-image, invariance or
invariant-cubic callback remains in this alternating consumer. -/
theorem sylow_normalizer_le_of_alternating_six_residual_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : ((blockLocalResidual T L).subgroupOf (L ⊔ (T : Subgroup G))).map
      (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) = K) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hi := blockLocalInvariance_of_alternating h D hfixed hb
  obtain ⟨d, ho, hd, hout, hmove, hnormal, _⟩ :=
    exists_odd_alternating_omega_movement h D hescape hi hb
  obtain ⟨marking⟩ :=
    alternating_six_local_marking_of_residual_image h D hfixed hb hd hescape hmove hnormal m hρ hX
  exact false_of_alternating_six_marking_original h D hfixed hb ho hd hout marking

/-- The source-module splitting reduces the remaining residual-image premise
to the centralizer of the Sylow-fixed subgroup of the intrinsic block layer.
The final owner `qt-d-12216-normalizer-block-centralizer` retains construction
of compatible coordinates for this model calculation. -/
theorem sylow_normalizer_le_of_alternating_six_sylow_fixed_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsAlternatingBlock L 6)
    {ρ : ChapterC.AlternatingSixBlockAction.Actor →*
      MulAut (Multiplicative ChapterC.AlternatingSixBlockAction.Vector)}
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)
    (hX : let C := L ⊓ centralizer ((ChapterC.blockU L).map L.subtype ⊓
          centralizer (T : Set G) : Subgroup G)
      (((pResidual 2 C).map C.subtype).subgroupOf (L ⊔ (T : Subgroup G))).map
        (ChapterC.AlternatingSixBlockAction.joinPermutation D.sylow_normalizes_component m hρ) = K) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  apply hescape
  apply sylow_normalizer_le_of_alternating_six_residual_image h D hfixed hb m hρ
  rw [blockLocalResidual_eq_sylow_fixed_blockU h D hescape hb.2.1]
  exact hX


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
