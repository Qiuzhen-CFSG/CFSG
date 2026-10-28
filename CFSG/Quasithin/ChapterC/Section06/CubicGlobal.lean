module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicSingle
public import CFSG.Quasithin.ChapterC.Section06.CentralizerRank
public import CFSG.Quasithin.ChapterC.Section06.CubicSmallCore

/-!
# The original single A₃ global alternative of C.6.1

The genuine core determines which recognized H-model applies. When Q=U,
the self-centralizing four-group theorem gives the dihedral or semidihedral
overgroup. Otherwise the proved cubic Thompson stability and the two-member
family force the index-two overgroup to be all of Λ. The original rank,
core factorization, and every outside conjugate-family conclusion are
included on the same subgroups.

Source: Aschbacher--Smith C.6.1(1),(3),(5),(6a--b), pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

private theorem rankOne_global_of_stable
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hMΛ : M ≤ Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hJ : elementaryAbelianMaxJ M = elementaryAbelianMaxJ R) :
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



theorem cubic_global_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hK : IsAlternatingBlock K 3)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ) (hMΛ : M ≤ Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let N₀ := Λ ⊓ normalizer (R : Set G)
    let Q := H.pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    R.relIndex N₀ = 2 ∧ ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      primeRank 2 D ≤ 1 ∧ Q = K.pCoreIn 2 ⊔ D ∧
      (∀ y ∈ N₀, y ∉ R →
        elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧
        elementaryAbelianMaxSubgroups R = {Q,Q.map (MulAut.conj y⁻¹).toMonoidHom}) ∧
      ((R.relIndex Λ = 2 ∧ elementaryAbelianMaxJ R = elementaryAbelianMaxJ Λ ∧
          Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∨
        (Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧ (IsDihedralGroup Λ ∨ IsSemidihedralGroup Λ))) := by
  have hf := rankOne_family_from_original c h hi x hx hnc
  have hn := rankOne_normalizer_from_original c h Λ hΛ hRΛ hcontrol hi x hx hnc
  have hr := cubic_centralizer_rank_from_original c h hK hi x hx hnc
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
  refine ⟨hn.1,hf.2.1,hr.2.2,hf.2.2.2,?_,?_⟩
  · intro y hy hyr
    refine ⟨hn.2.2 y hy hyr,?_⟩
    have hp := thompson_normalizer_preserves_maxFamily_pair R (H.pCoreIn 2)
      ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) hf.2.2.1
      (normalizer_le_normalizer_elementaryAbelianMaxJ R ((normalizer (R : Set G)).inv_mem hy.2))
    have hmove : (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom ≠ H.pCoreIn 2 := by
      intro heq
      have hny : y⁻¹ ∈ normalizer (H.pCoreIn 2 : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
      have hny' : y ∈ normalizer (H.pCoreIn 2 : Set G) := by
        simpa only [inv_inv] using (normalizer (H.pCoreIn 2 : Set G)).inv_mem hny
      exact hyr (hctrl ▸ (show y ∈ Λ ⊓ normalizer (H.pCoreIn 2 : Set G) from ⟨hy.1,hny'⟩))
    rw [hp.resolve_left hmove]
    exact hf.2.2.1
  · by_cases hsmall : H.pCoreIn 2 = sourceModule K
    · exact Or.inr ⟨cubic_small_core_model_from_original c h hK hi x hx hnc hsmall,cubic_small_core_sylow c hK Λ hΛ hRΛ hcontrol hsmall⟩
    · have hg := rankOne_global_of_stable c h Λ hΛ hMΛ hcontrol hi x hx hnc (cubic_large_core_thompson_from_original c h hK hi x hx hnc hsmall)
      exact Or.inl ⟨hg.1,hg.2.1,(cubic_large_core_model_from_original c h hK hi x hx hnc hsmall).2⟩

end CFSG.Quasithin.ChapterC.Section06
