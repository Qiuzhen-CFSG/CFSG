module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer.Action

/-!
# The literal Thompson and Baumann images in the original hexacode action

The original maximum elementary family has a moving member. Uniqueness of
hexacode best offenders inside one two-group identifies its entire Thompson
image. The pointwise-kernel calculation then identifies the Baumann image.

Source: Aschbacher–Smith, B.4.2(8) and the covered-six paragraph of 13.6.22.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
open ComponentSelection
variable {G : Type*} [Group G] [Finite G] {K L T U : Subgroup G} {z v : G}
    {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)} [IsElementaryAbelian 2 U]
    (d : Model K L T U z v hL hz)

theorem Model.model_best {B : Subgroup (Gplus K L T z v hL hz)}
    (hB : IsBestOffender d.action B) :
    IsBestOffender Hexacode.action (B.map d.embedding) :=
  hB.map_of_fixedCodim d.action Hexacode.action d.embedding d.injective
    (fixedCodim_map_equivariant d.action Hexacode.action d.embedding
      d.coordinates d.intertwining)

/-- Every nontrivial maximum-elementary image is the same offender in the actual Tᵥ-image;
the subgroup they generate is therefore itself a best offender. -/
theorem Model.thompson_isBestOffender (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hUT : U ≤ Tv T v) (hUN : plusActor K L T v ≤ normalizer (U : Set G)) :
    IsBestOffender d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) := by
  obtain ⟨E, hE, hEn⟩ := AlternatingBranches.CoveredSix.ThompsonImage.exists_maximum_moving K L T z v hK hn hL hz
  let B := plusImage K L T z v hL hz E
  have hB : IsBestOffender d.action B :=
    d.maxElementary_isBestOffender hUT hUN E hE hEn
  have hT : IsPGroup 2 (Tv T v) := by
    obtain ⟨P, hP⟩ := hK.1.2.2.1
    rw [← hP]
    exact P.isPGroup'.map (K ⊔ Tv T v).subtype
  let P := (plusImage K L T z v hL hz (Tv T v)).map d.embedding
  have hP : IsPGroup 2 P :=
    (hT.comap_subtype.map (plusMk K L T z v hL hz)).map d.embedding
  have hBP : B.map d.embedding ≤ P := map_mono (map_mono (comap_mono hE.1))
  have hEP (D : Subgroup G) (hD : D ∈ elementaryAbelianMaxSubgroups (Tv T v)) :
      plusImage K L T z v hL hz D ≤ B := by
    by_cases hDn : plusImage K L T z v hL hz D = ⊥
    · rw [hDn]; exact bot_le
    have hD' := d.maxElementary_isBestOffender hUT hUN D hD hDn
    have he := Hexacode.bestOffender_unique_in_pgroup P hP
      (map_mono (map_mono (comap_mono hD.1))) hBP (d.model_best hD') (d.model_best hB)
    exact (map_injective d.injective he).le
  have hJB : elementaryAbelianMaxJ (Tv T v) ≤
      (B.comap (plusMk K L T z v hL hz)).map (plusActor K L T v).subtype := by
    apply sSup_le
    intro D hD g hg
    refine ⟨⟨g, (hD.1.trans (show Tv T v ≤ plusActor K L T v from le_sup_right)) hg⟩, ?_, rfl⟩
    exact hEP D hD (mem_map_of_mem _ hg)
  have hJ : plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) = B := by
    apply le_antisymm
    · rintro a ⟨g, hg, rfl⟩
      obtain ⟨b, hb, he⟩ := hJB hg
      have hbg : b = g := Subtype.ext he
      exact hbg ▸ hb
    · exact map_mono (comap_mono (le_sSup hE))
  rw [hJ]
  exact hB
/-- The full best-offender kernel calculation survives the prescribed coordinates. -/
theorem Model.bestOffender_kernel
    {B : Subgroup (Gplus K L T z v hL hz)} (hB : IsBestOffender d.action B) :
    subspaceKernel d.action (fixedSpace d.action B) ⊤ = B := by
  have hmodel := d.model_best hB
  have hfixed := fixedSpace_map_equivariant d.action Hexacode.action
    d.embedding d.coordinates d.intertwining B
  apply le_antisymm
  · intro g hg
    have hgm : d.embedding g ∈ B.map d.embedding := by
      rw [Hexacode.bestOffender_eq_kernel _ hmodel]
      refine ⟨mem_top _, ?_⟩
      intro w hw
      rw [← hfixed] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      exact (d.intertwining g u).symm.trans (congrArg d.coordinates (hg.2 u hu))
    obtain ⟨b, hb, he⟩ := hgm
    exact d.injective he ▸ hb
  · intro g hg
    exact ⟨mem_top _, fun u hu => hu ⟨g, hg⟩⟩

/-- Baumann fixes the Thompson-fixed vectors in U(K). Only containment of
the elementary block layer in Tᵥ is needed from the earlier Sylow setup. -/
theorem Model.baumann_fixes
    (hUT : U ≤ Tv T v) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      subspaceKernel d.action
        (fixedSpace d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))) ⊤ := by
  rintro b ⟨g, hg, rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro u hu
  have hJS : elementaryAbelianMaxJ (Tv T v) ≤ Tv T v := sSup_le fun _ hA => hA.1
  have huC := (d.mem_fixedSpace_image _ (hJS.trans le_sup_right) u).mp hu
  have hu2 : (u.toMul : G) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _ u.toMul.property
  let : IsElementaryAbelian 2 (zpowers (u.toMul : G)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hu2
  have huOmega := elementary_centralizer_maxJ_le_omegaCenter (Tv T v)
    (zpowers (u.toMul : G))
    (zpowers_le.mpr (hUT u.toMul.property))
    (zpowers_le.mpr huC) (mem_zpowers (u.toMul : G))
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [d.action_conjugation]
  have hc := hg.2 _ huOmega
  change (u.toMul : G) * (g : G) = (g : G) * (u.toMul : G) at hc
  rw [← hc, mul_inv_cancel_right]

/-- Recognizing the full pointwise kernel discharges the Baumann-image
identity on the original U(K), without a splitting assumption on W_K. -/
theorem Model.baumann_eq_thompson
    (hUT : U ≤ Tv T v)
    (hk : subspaceKernel d.action
      (fixedSpace d.action (plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)))) ⊤ =
        plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v)) := by
  apply le_antisymm ((d.baumann_fixes hUT).trans hk.le)
  apply map_mono
  apply comap_mono
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj w hw
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 j hj).symm


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
