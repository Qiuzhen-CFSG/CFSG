module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.Ordering
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.CommonNormal

/-!
# The central Thompson branch after C_G(Z)=T

When J(T) centralizes V(H), Baumann heredity identifies Baum(T) with
Baum(O₂(H)), so H normalizes the original Baumann subgroup. For a maximal
local M this gives N_G(Baum(T))=M. Consequently an outside minimal local
cannot have the Baumann Sylow conclusion: the genuine universal 3.1.1
would supply a nontrivial common normal two-subgroup.

This is the normalizer and final common-normal part of the source
14.1.4/15.4.6 argument in the stronger 15.4.8 setting. The original outside
minimal-parabolic application of B.6.10 remains to supply its Sylow
conclusion; no such conclusion is asserted here. Source: Aschbacher–Smith,
printed pp.976,1158,1160.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource ModuleStructure
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem core_le_T (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : H.pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
    pCoreIn_le_sylow H (T.subtype hTH)

omit [Finite G] in
/-- The nontrivial Sylow center lies in its original Baumann subgroup. -/
theorem omega_le_baumann (T : Sylow 2 G) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ ChapterB.baumann (T : Subgroup G) := by
  intro z hz
  obtain ⟨hzT, _, hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  refine ⟨hzT, ?_⟩
  intro a ha
  have haJ := ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  exact hzc a (hJT haJ)

/-- Baumann heredity identifies the same subgroup inside the actual local core. -/
theorem baumann_eq_core_of_central
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hH : HasCharacteristicTwo H)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T H, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (H.pCoreIn 2) := by
  let := localV_elementary T H hTH hH
  have hJ := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcentral)
  have hCT : (T : Subgroup G) ⊓ centralizer (localV T H : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hTH).trans (localV_centralizer T H hTH hC).le
    · exact le_inf (core_le_T T H hTH)
        ((localV_centralizer T H hTH hC).ge.trans inf_le_right)
  exact (ChapterB.lemma_B_2_3_5 (T : Subgroup G) (localV T H)
    (localV_le_sylow T H hTH hH) hJ).trans (congrArg ChapterB.baumann hCT)

/-- Central Thompson action forces H to normalize the original Baumann subgroup. -/
theorem normalizes_baumann_of_central
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hH : HasCharacteristicTwo H)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T H, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥) :
    H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  rw [baumann_eq_core_of_central T H hTH hH hC hcentral]
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 H).le_normalizer_map H.subtype
  exact hHN.trans (normalizer_le_normalizer_baumann _)

/-- In a maximal local, the central branch determines the full ambient Baumann normalizer. -/
theorem normalizer_baumann_eq_of_central {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) = M := by
  have hSne : ChapterB.baumann (T : Subgroup G) ≠ ⊥ := by
    intro he
    exact centralOmega_ne_bot hG T (le_bot_iff.mp (he ▸ omega_le_baumann T))
  have hS2 := T.isPGroup'.to_le (show ChapterB.baumann (T : Subgroup G) ≤
    (T : Subgroup G) from inf_le_left)
  have hMN := normalizes_baumann_of_central T M hTM
    (hG.evenCharacteristic T M hM hTM) hC hcentral
  exact (hM.eq_of_le ⟨_, hSne, hS2, rfl⟩ hMN).symm

/-- After 15.4.8 the global alpha centralizer is exactly the original Baumann subgroup. -/
theorem centralizer_alpha_eq_baumann (T : Sylow 2 G)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    centralizer (ChapterB.thompsonAlpha (T : Subgroup G) : Set G) =
      ChapterB.baumann (T : Subgroup G) := by
  let := omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hZJ : omegaOneCenterAmbient (T : Subgroup G) ≤
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j (hJT hj)
  have hZE := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G)
    (omegaOneCenterAmbient (T : Subgroup G)) hZT hZJ
  have hET := (centralizer_le hZE).trans hC.le
  exact le_antisymm (le_inf hET le_rfl) inf_le_right

/-- Thus every ambient normalizer of the actual Thompson subgroup normalizes Baum(T). -/
theorem normalizer_thompson_le_normalizer_baumann (T : Sylow 2 G)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  have hNE : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      normalizer (ChapterB.thompsonAlpha (T : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := mem_normalizer_iff_map_conj_eq.mp hg
    change (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom = _ at he
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))).map
      (MulAut.conj g).toMonoidHom = _
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective, he]
    rfl
  rw [← centralizer_alpha_eq_baumann T hC]
  exact hNE.trans (normalizer_le_normalizer_centralizer _)

/-- The ambient Thompson normalizer lies in the same maximal local in the central case. -/
theorem normalizer_thompson_le_of_central {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M :=
  (normalizer_thompson_le_normalizer_baumann T hC).trans_eq
    (normalizer_baumann_eq_of_central hG T M hM hTM hC hcentral)

/-- Every outside minimal local in the central branch has genuine noncentral
Thompson action on its own omega-center closure. -/
theorem outside_thompson_moved_of_central {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M H : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ⁅localV T H, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ := by
  intro hzero
  have hHN := normalizes_baumann_of_central T H hH.1.1.2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1))
    hC hzero
  exact hH.1.2 (hHN.trans_eq (normalizer_baumann_eq_of_central hG T M hM hTM hC hcentral))

/-- The same outside group is an actual minimal parabolic: otherwise normality
of T would force normalization of Baum(T) and containment in M. -/
theorem outside_minimalParabolic_of_central {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M H : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.IsMinimalParabolicOver T H := by
  apply Chapter3.HStar.minimalParabolic T hTM hH
  right
  intro hn
  have hHN := (normal_subgroupOf_iff_le_normalizer hH.1.1.2).mp hn
  exact hH.1.2 ((hHN.trans (normalizer_le_normalizer_baumann _)).trans_eq
    (normalizer_baumann_eq_of_central hG T M hM hTM hC hcentral))

/-- The precise 3.1.1 contradiction for the actual outside minimal local.
The remaining Baumann Sylow premise is the original B.6.10 application. -/
theorem outside_not_baumann_sylow_of_central
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (earlier311 : RatioSource.Earlier311 (G := G))
    (T : Sylow 2 G) (M H : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hcentral : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      ((pResidual 2 H).map H.subtype ⊔ ChapterB.baumann (T : Subgroup G)) := by
  intro hs
  have hSle : ChapterB.baumann (T : Subgroup G) ≤ (T : Subgroup G) := inf_le_left
  have hSne : ChapterB.baumann (T : Subgroup G) ≠ ⊥ := by
    intro he
    exact centralOmega_ne_bot hG T (le_bot_iff.mp (he ▸ omega_le_baumann T))
  have hN := normalizer_baumann_eq_of_central hG T M hM hTM hC hcentral
  have hcommon := earlier311 T hG M H _ ⟨Chapter1.mem_H_of_isTwoLocal hM.1, hTM⟩
    hH.1.1 (Chapter3.HStar.hasUniqueMaximalOver T hTM hH) hSne hSle hs hN.ge
  exact Chapter3.no_common_normal_of_unique_maximal (T.isPGroup'.to_le hSle)
    (fun N hN hMN => (hM.eq_of_le hN.1 hMN).symm) hH.1.2 hcommon

end CFSG.Quasithin.Chapter15.Section04.InitialSource
