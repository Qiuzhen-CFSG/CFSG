module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedWeakClosure
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.SylowCentralizer
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterSourceExits
import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerSetup
import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
import Theory.GroupTheory.TwoPerfectNormalizerControl

/-!
# The original contained triple-six Sylow centralizer is trivial

If the actual C_T(K) were nontrivial, original local uniqueness would put
the centralizer of Ω₁Z(T) in N_G(K). The earlier source-exit theorem then
gives a noncommuting conjugate of U. Sylow positioning preserves U and
puts that conjugate in T, contradicting the proved original weak closure.

Only the same original guarded earlier HStar exits and seven exclusion
are retained. The whole-module restriction, point fusion, rank parameters
and weak-closure construction are supplied by their proved source APIs.
Source: Aschbacher--Smith12.7.12, printed p.843, using12.2.9 and12.4.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual Sylow centralizer vanishes, with the genuine earlier
source obligations restricted to the original ambient group and T. -/
theorem original_tripleSix_contained_sylow_centralizer
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
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
  let := D.elementary
  by_contra hn
  have hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (K : Set G) := by
    rw [sylowCenterSeed_eq]
    exact RecognitionSource.FusionReducibleNormalizer.omega_centralizer_le_of_sylow_centralizer
      h D hn
  have hs : 1 < globalS U := by
    rw [(original_tripleSix_contained_rank_parameters h structural D a t ht heven contained).2]
    norm_num
  obtain ⟨g,hne,hle⟩ := noncommutingConjugate_of_source_exits_at
    h D structural modules hmany hZ seven exits hs
  have hTU := ((structural K h).2.2 U D).1
  obtain ⟨g',hg',hne'⟩ := Preliminaries.position_noncommuting_conjugate
    T U (IsElementaryAbelian.isPGroup 2 U) hTU g hne (hle.trans inf_le_left)
  have hW := (original_tripleSix_contained_weakClosure
    h structural D a t ht heven contained).1
  apply hne'
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact (gamma_le_weakClosure ((mem_gamma_zero_iff U (T : Subgroup G) _).mpr
    ⟨g',rfl,hg'⟩)).trans (hW.trans inf_le_right)

/-- Characteristic two upgrades the actual Sylow-centralizer vanishing
to the full ambient component centralizer. -/
theorem original_tripleSix_contained_component_centralizer
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
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    centralizer (K : Set G) = ⊥ := by
  have hCT := original_tripleSix_contained_sylow_centralizer
    h structural modules D a t ht heven contained hmany seven exits
  let M := normalizer (K : Set G)
  let C := centralizer (K : Set G)
  have hmax := h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hNM := h.source_chosen_normalizer_le_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) D
  have hCM : C ≤ M := (centralizer_le D.le_component).trans
    ((centralizer_le_normalizer U).trans hNM)
  have hMC : M ≤ normalizer (C : Set G) := normalizer_le_normalizer_centralizer K
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hmax.1.1 D.sylow_normalizes_component)
  by_contra hn
  have hcore : pCore 2 C ≠ ⊥ := pCore_ne_bot_of_core_normalizes M C hCM hchar
    ((pCoreIn_le 2 M).trans hMC) hn
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hzero : C.pCoreIn 2 = ⊥ := bot_unique
    ((le_inf ((pCoreIn_mono_of_normalizes hCM hMC).trans hQT)
      (pCoreIn_le 2 C)).trans_eq hCT)
  exact hcore (((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp hzero)

end CFSG.Quasithin.Chapter12.Section07
