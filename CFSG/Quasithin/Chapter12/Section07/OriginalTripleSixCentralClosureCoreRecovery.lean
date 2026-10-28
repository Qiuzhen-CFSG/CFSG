module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSecondaryCore
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter3.Section02

/-!
# The original central-closure core and full normalizer

The actual secondary-module contradiction gives O2(KT)=U. Characteristic
two and the original maximal two-local apply3.2.11 to recover the full
module centralizer and both normalizers. The original hexacode automizer
bounds the index over K by two; the supplied Sylow then forces N_G(K)=KT.
All conclusions concern the original subgroups in G.

Source: Aschbacher--Smith12.7.20 and12.7.6(2), printed pp.846 and840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original chosen module is the whole core and full ambient module
centralizer; its two normalizers are exactly the original Sylow join. -/
theorem original_tripleSix_central_closure_core_recovery
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    K.pCoreIn 2 = U ∧ (K ⊔ (T : Subgroup G)).pCoreIn 2 = U ∧
      (normalizer (K : Set G)).pCoreIn 2 = U ∧
      normalizer (U : Set G) = normalizer (K : Set G) ∧
      centralizer (U : Set G) = U ∧
      normalizer (K : Set G) = K ⊔ (T : Subgroup G) := by
  let H := K ⊔ (T : Subgroup G)
  let M := normalizer (K : Set G)
  have hHN : H ≤ M := sup_le K.le_normalizer D.sylow_normalizes_component
  have hQ : H.pCoreIn 2 = U := original_tripleSix_central_closure_secondary_core_eq
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hK : K.pCoreIn 2 = U := le_antisymm
    ((pCoreIn_mono_of_normalizes (show K ≤ H from le_sup_left) hHN).trans_eq hQ)
    D.le_componentCore
  have hmax := h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hmax.1.1 D.sylow_normalizes_component)
  let := D.elementary
  obtain ⟨hM,hN,hC,_⟩ := Chapter3.Section02.lemma_3_2_11_of_core_containment T K H M U
    le_sup_right hHN K.le_normalizer rfl hmax.1 hchar hQ.symm D.le_componentCore D.ne_bot
  obtain ⟨f,hf,_,himage,_⟩ := original_tripleSix_full_automizer h structural D a
  let A := inducedAutomizer U K
  have htwo : hexSign.ker.index = 2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
    simp [Nat.card_eq_fintype_card]
  have ha : A.index ∣ 2 := by
    have hh := A.index_map_of_injective hf
    rw [himage,htwo] at hh
    exact ⟨f.range.index,hh⟩
  let N := normalizer (U : Set G)
  have hk : U.normalizerMonoidHom.rangeRestrict.ker ≤ K.subgroupOf N := by
    rw [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker]
    exact subgroupOf_mono N (hC.le.trans D.le_component)
  have hi : A.index = K.relIndex M := by
    rw [show A = (K.subgroupOf N).map U.normalizerMonoidHom.rangeRestrict from rfl,
      (K.subgroupOf N).index_map_eq U.normalizerMonoidHom.rangeRestrict_surjective hk]
    change K.relIndex N = K.relIndex M
    rw [show N=M from hN]
  have hd : H.relIndex M ∣ 2 :=
    (relIndex_dvd_of_le_left M (show K ≤ H from le_sup_left)).trans (hi ▸ ha)
  have hn : ¬ 2 ∣ H.relIndex M := by
    intro hh
    exact T.not_dvd_index (hh.trans ((relIndex_dvd_index_of_le hHN).trans
      (index_dvd_of_le (show (T : Subgroup G) ≤ H from le_sup_right))))
  have he : H.relIndex M = 1 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right
    (fun he => hn (he ▸ dvd_rfl))
  exact ⟨hK,hQ,hM,hN,hC,le_antisymm (relIndex_eq_one.mp he) hHN⟩

end CFSG.Quasithin.Chapter12.Section07
