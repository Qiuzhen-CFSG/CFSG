module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalHypotheses
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.ModuleLayers
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.GroupTheory.PGroup.ThompsonPairNormalizer

/-!
# The literal rank-one core and family in C.6.1

When R is the original Sylow subgroup and K=O²(H) is one block, the
centralizer of U(K) in R is O₂(H). The proved C.5.6 terminal identifies
this with the marked core of K Baum(R). Thus the two-member elementary
family and Thompson span concern the original O₂(H), not a replacement
core. The original normalizer obstruction then gives index two in N_Λ(R).

The marked C.5 setup and preceding escaping conjugate are explicit here;
the Chapter 2 consumer constructs both from the original source data.
Source: Aschbacher--Smith C.6.1(1),(3),(5), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]
variable {H M K R : Subgroup G}

theorem original_core_eq_module_centralizer
    (c : OriginalHypotheses H M K R R) (hk : IsShort K) :
    R ⊓ centralizer (sourceModule K : Set G) = H.pCoreIn 2 := by
  let L := pResidual 2 H
  let e : L ≃* K := (equivMapOfInjective L H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr c.residual)
  have hL : IsBlock L := ⟨inferInstance,
    ChapterC.RankOne.Solvable.isShort_of_equiv e.symm hk,
    (inferInstance : L.Normal).isSubnormal⟩
  have hf : generalizedFitting L = pCore 2 L :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore L c.fitting le_normalizer_of_normal
  have hc : centralizer (moduleLayer L : Set H) ≤ pCore 2 H :=
    centralizer_blockU_le_core_of_normal L hf (isPGroup_quotient_pResidual 2)
  have hm : (moduleLayer L).map H.subtype = sourceModule K := by
    rw [←moduleLayer_map H.subtype H.subtype_injective,c.residual]
    rfl
  apply le_antisymm
  · rintro g ⟨hg,hgu⟩
    have hgi : (⟨g,c.R_le_H hg⟩ : H) ∈ pCore 2 H := by
      apply hc
      intro u hu
      exact Subtype.ext (hgu u (hm ▸ mem_map_of_mem H.subtype hu))
    exact mem_map_of_mem H.subtype hgi
  · apply le_inf
    · simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
    · rw [←hm]
      exact (map_mono hL.core_centralizes_blockU).trans
        (map_centralizer_le_centralizer_image _ H.subtype)

theorem rankOne_family_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    RankOne.Q R K = H.pCoreIn 2 ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      elementaryAbelianMaxSubgroups R =
        {H.pCoreIn 2,(H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom} ∧
      H.pCoreIn 2 = K.pCoreIn 2 ⊔ (R ⊓ centralizer (K : Set G)) := by
  have hRK : R ≤ normalizer (K : Set G) := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hphi := h.frattini_eq_bot_of_index_two H M R c.T_le c.R_normal hRK hH hno
    hi x hx hnc
  have he := h.source_single_block_terminal_equalities c.R_twoGroup H M R le_rfl c.T_le
    c.R_normal hRK hH hno x hx hi hnc
  have hcore : RankOne.Q R K = H.pCoreIn 2 :=
    h.core.trans (he.2.1.symm.trans (original_core_eq_module_centralizer c h.short))
  have hp := h.source_single_block_terminal c.R_twoGroup H M R le_rfl c.T_le
    c.R_normal hRK hH hno x hx hi hnc
  refine ⟨hcore,h.baumann_eq_thompson (c.R_normal hx) hnc hphi,?_,?_⟩
  · simpa only [hcore] using h.sylow_maximum_family (c.R_normal hx) hnc hphi
  · rw [←original_core_eq_module_centralizer c h.short]
    change R ⊓ centralizer (RankOne.U K : Set G) = K.pCoreIn 2 ⊔ _
    rw [hp.2.1,hp.1]

theorem rankOne_normalizer_from_original
    (c : OriginalHypotheses H M K R R)
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    R.relIndex (Λ ⊓ normalizer (R : Set G)) = 2 ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      ∀ y ∈ Λ ⊓ normalizer (R : Set G), y ∉ R →
        elementaryAbelianMaxJ R = H.pCoreIn 2 ⊔
          (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom := by
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
  have hh := twoGroup_normalizer_index_two_of_maxFamily_pair Λ R (H.pCoreIn 2)
    ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) hΛ hRΛ hf.2.2.1
    (hcontrol _ hQ hQR hnQ)
  exact ⟨hh.1,hf.2.1,hh.2⟩

end CFSG.Quasithin.ChapterC.Section06
