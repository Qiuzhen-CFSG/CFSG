module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section06.Thompson.Original

/-!
# The natural-block global conclusion of C.6.1

The genuine natural action proves J(M₀)=J(R). Its two-member maximum
elementary family and the original normalizer condition then force M₀=Λ.
Consequently R has index two in Λ, both Thompson subgroups agree, and every
element outside R gives the same original core pair and its Thompson span.
The two-core factorization is retained on H and O²(H).

Source: Aschbacher--Smith C.6.1(1),(3),(5),(6a), pp.164--165.
The rank bound on C_R(O²(H)) is a separate assertion of (3).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

theorem natural_global_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    {n : ℕ} (hK : IsL2EvenBlock K n)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hMΛ : M ≤ Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    R.relIndex Λ = 2 ∧ elementaryAbelianMaxJ R = elementaryAbelianMaxJ Λ ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      H.pCoreIn 2 = K.pCoreIn 2 ⊔ (R ⊓ centralizer (K : Set G)) ∧
      ∀ y ∈ Λ, y ∉ R →
        elementaryAbelianMaxJ R = H.pCoreIn 2 ⊔
          (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom ∧
        elementaryAbelianMaxSubgroups R =
          {H.pCoreIn 2,(H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom} ∧
        elementaryAbelianMaxSubgroups Λ =
          {H.pCoreIn 2,(H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom} := by
  have hf := rankOne_family_from_original c h hi x hx hnc
  have hJ := rankOne_thompson_stable_from_original c h hK hi x hx hnc
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hu := h.module_le_core
    rw [hf.1,hb] at hu
    exact moduleLayer_ne_bot h.short (bot_unique hu)
  have hQR : H.pCoreIn 2 ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hctrl := hcontrol _ hQ hQR hnQ
  have he : M = Λ := twoGroup_eq_of_index_two_thompson_pair Λ M R (H.pCoreIn 2)
    ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) hΛ c.T_le hMΛ hi hf.2.2.1 hctrl hJ
  have hJΛ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ Λ := he ▸ hJ.symm
  refine ⟨he ▸ hi,hJΛ,hf.2.1,hf.2.2.2,?_⟩
  intro y hy hyr
  have hyR : y⁻¹ ∈ normalizer (R : Set G) :=
    c.R_normal (he.symm ▸ Λ.inv_mem hy)
  have hp := thompson_normalizer_preserves_maxFamily_pair R (H.pCoreIn 2)
    ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) hf.2.2.1
    (normalizer_le_normalizer_elementaryAbelianMaxJ R hyR)
  have hmove : (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom ≠ H.pCoreIn 2 := by
    intro heq
    have hn : y⁻¹ ∈ normalizer (H.pCoreIn 2 : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
    have hn' : y ∈ normalizer (H.pCoreIn 2 : Set G) := by
      simpa only [inv_inv] using (normalizer (H.pCoreIn 2 : Set G)).inv_mem hn
    exact hyr (hctrl ▸ (show y ∈ Λ ⊓ normalizer (H.pCoreIn 2 : Set G) from ⟨hy,hn'⟩))
  have hmap := hp.resolve_left hmove
  have hfy : elementaryAbelianMaxSubgroups R =
      {H.pCoreIn 2,(H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom} := by
    rw [hmap]
    exact hf.2.2.1
  refine ⟨?_,hfy,?_⟩
  · rw [elementaryAbelianMaxJ,hfy,sSup_pair]
  · rw [←maxFamily_thompson Λ,←hJΛ,maxFamily_thompson R,hfy]

end CFSG.Quasithin.ChapterC.Section06
