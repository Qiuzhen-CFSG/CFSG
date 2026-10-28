module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# Characteristic two for the literal generic parabolics

The nontrivial residual K=O²(H) is normal in the characteristic-two
group H. Characteristic-two inheritance makes its own two-core nontrivial,
so N_G(K) is again a Sylow overgroup with nontrivial two-core. The cores
of N_G(L) and N_G(K) both lie in S=O₂(N_G(L)∩H). Consequently any
subgroup of the corresponding normalizer containing S has characteristic
two, by the original core-centralizer criterion 1.1.4(4).

This discharges both intrinsic generalized-Fitting equalities for the
source parabolics once the right factor and its Borel product are supplied.
`RightFactor` is the remaining construction target for 5.1.10--11 and
5.2.1--4; it is not asserted to exist here. It retains the actual Sylow,
quotient model, containment, escape and Cartan action.

Source: Aschbacher--Smith, 1.1.3--4, printed pp.500--501, and the
verification of F.1.1(f) on p.650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_eq_of_core_le {M Y : Subgroup G}
    (hM : M ∈ Chapter1.He G) (hYM : Y ≤ M) (hc : M.pCoreIn 2 ≤ Y) :
    generalizedFitting Y = pCore 2 Y := by
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  apply Chapter1.mem_He_iff.mp
  exact pCoreIn_selfCentralizing_of_core_centralizer_le hM hYM (inf_le_left.trans hc)

/-- The actual residual normalizer has characteristic two before selecting L₂. -/
theorem residual_normalizer_mem_He {κ : GroupClass} {T : Sylow 2 G} {L H W : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    normalizer (residual H : Set G) ∈ Chapter1.He G := by
  have hKH : residual H ≤ H := map_subtype_le _
  have hKne : residual H ≠ ⊥ := by
    intro hb
    exact residual_not_le T H _ hH.1.1.2 h.sylow_normalizes hH.1.2 (hb ▸ bot_le)
  have hHchar := Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1
  let hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hKchar := Chapter1.lemma_1_1_3_1 hHchar hKne hKH hn.isSubnormal
  have hc : (residual H).pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hh : residual H ≤ ⊥ := by
      change residual H ⊓ centralizer ((residual H).pCoreIn 2 : Set G) ≤ (residual H).pCoreIn 2 at hKchar
      have hz : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
      simpa only [hb, hz, inf_top_eq] using hKchar
    exact hKne (bot_unique hh)
  have hNN : normalizer (residual H : Set G) ≤
      normalizer ((residual H).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image _ (pCore 2 (residual H))
  have hcoreN : (residual H).pCoreIn 2 ≤
      (normalizer (residual H : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((pCoreIn_le 2 _).trans (residual H).le_normalizer) hNN
  apply Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
  exact ⟨fun hb => hc (bot_unique (hb ▸ hcoreN)),
    hH.1.1.2.trans (le_normalizer_residual H)⟩

/-- Containing S inside N_G(L) supplies the intrinsic generalized-Fitting equality. -/
theorem characteristic_two_of_sourceS_left {κ : GroupClass} {T : Sylow 2 G}
    {L H W Y : Subgroup G} {n : ℕ} (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ≤ normalizer (L : Set G))
    (hSY : sourceS L H ≤ Y) : generalizedFitting Y = pCore 2 Y := by
  apply fitting_eq_of_core_le
    (Chapter1.mem_He_iff.mpr (h.qtke.evenCharacteristic T _ h.maximal h.sylow_normalizes)) hY
  exact (Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hTH)
    (show intersection L H ≤ normalizer (L : Set G) from inf_le_left)).trans hSY

/-- Containing S inside N_G(O²(H)) supplies the same intrinsic equality. -/
theorem characteristic_two_of_sourceS_right {κ : GroupClass} {T : Sylow 2 G}
    {L H W Y : Subgroup G} {n : ℕ} (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ≤ normalizer (residual H : Set G)) (hSY : sourceS L H ≤ Y) :
    generalizedFitting Y = pCore 2 Y := by
  apply fitting_eq_of_core_le (residual_normalizer_mem_He h hH) hY
  exact (Chapter3.twoCore_le_of_sylow_le T hH.1.1.2 (le_normalizer_residual H)).trans
    ((Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2)
      (show intersection L H ≤ H from inf_le_right)).trans hSY)

/-- Construction target for the right factor in 5.1.10--11 and 5.2.1--4.
The source producer must select this factor inside the actual residual;
no uniqueness, characteristic-two or faithful-amalgam conclusion is assumed. -/
structure RightFactor (T : Sylow 2 G) (L H A B L₂ : Subgroup G) : Prop where
  le_residual : L₂ ≤ residual H
  outside : ¬ L₂ ≤ normalizer (L : Set G)
  sylow : ∃ P : Sylow 2 L₂,
    (P : Subgroup L₂).map L₂.subtype = sourceS L H ⊓ L₂
  quotient : ChapterF.Source.IsRankOneModel (L₂ ⧸ pCore 2 L₂)
  S_normalizes : sourceS L H ≤ normalizer (L₂ : Set G)
  cartan_normalizes : A ≤ normalizer (L₂ : Set G)
  borel : ChapterF.Source.borel L₂ (sourceS L H) =
    (sourceS L H ⊓ L₂) ⊔ (B ⊓ L₂)

/-- The source local factors and Borel product give characteristic two for both literal parabolics. -/
theorem RightFactor.characteristic_two {κ : GroupClass} {T : Sylow 2 G}
    {L H W A B L₂ : Subgroup G} {n : ℕ} (r : RightFactor T L H A B L₂)
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hleft : sourceS L H ⊓ L = (T : Subgroup G) ⊓ L)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ∀ i : Fin 2, generalizedFitting (ChapterF.Source.parabolic ![L, L₂] (sourceS L H) i) =
      pCore 2 (ChapterF.Source.parabolic ![L, L₂] (sourceS L H) i) := by
  have hSM : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans h.sylow_normalizes
  have hSK : sourceS L H ≤ normalizer (residual H : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans
      (hH.1.1.2.trans (le_normalizer_residual H))
  intro i
  fin_cases i
  · apply characteristic_two_of_sourceS_left h hH.1.1.2
    · change L ⊔ sourceS L H ⊔ ChapterF.Source.borel L₂ (sourceS L H) ≤ _
      rw [r.borel]
      exact sup_le (sup_le L.le_normalizer hSM)
        (sup_le (inf_le_left.trans hSM) (inf_le_left.trans (c.right_le.trans inf_le_left)))
    · exact le_sup_right.trans le_sup_left
  · apply characteristic_two_of_sourceS_right h hH
    · change L₂ ⊔ sourceS L H ⊔ ChapterF.Source.borel L (sourceS L H) ≤ _
      have hb : ChapterF.Source.borel L (sourceS L H) = localBorel T L := by
        unfold ChapterF.Source.borel localBorel
        rw [hleft]
      rw [hb]
      exact sup_le (sup_le (r.le_residual.trans (residual H).le_normalizer) hSK) hN
    · exact le_sup_right.trans le_sup_left

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
