module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.SourceInputs
public import CFSG.Quasithin.ChapterE.Section03.Parameters.ReducedAction
public import CFSG.Quasithin.ChapterE.Section03.OddCore.SolvableApplication
public import Theory.GroupTheory.ReducedNormal.ComponentSeedSplitting
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd

/-!
# The literal local omega module in 12.4.1

Characteristic two makes U=⟨Ω₁Z(T)ᴴ⟩ reduced. The residual supplement
H=O²(H)T identifies this with the source's V_K, and the central Sylow seed
splits off the fixed part. In an escaping H-star group, the normal
centralizer of U misses the residual. The minimal-parabolic core then gives
C_T(U)=O₂(H); if T is normal in H, this containment is immediate.
Reducedness transfers to the actual induced automizer, and E.4.1 proves
the parameter bound for solvable H on the whole U.

Source: Aschbacher–Smith 12.2.7(1), 12.3.2 and 12.4.1, pp.797,807,812;
B.2.14 and B.6.8. The source controls C_T(U), not the whole C_H(U).
The nonsolvable classification and its parameter computation remain with
qt-d-1241-l3-conjugate; qt-d-1242-l3-commutator-source owns final assembly.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

omit [Finite G] in
/-- Agreement of the two ambient presentations of Ω₁Z(T). -/
theorem sylowCenterSeed_eq (T : Sylow 2 G) :
    sylowCenterSeed T = omegaCenterIn (T : Subgroup G) :=
  (omegaCenterIn_eq_omegaOneAmbient _).symm

omit [Finite G] in
theorem sylowCenterSeed_le (T : Sylow 2 G) : sylowCenterSeed T ≤ (T : Subgroup G) := by
  rw [sylowCenterSeed_eq]
  exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1

omit [Finite G] in
theorem sylowCenterSeed_centralizes (T : Sylow 2 G) :
    sylowCenterSeed T ≤ centralizer (T : Set G) := by
  rw [sylowCenterSeed_eq]
  exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1

omit [Finite G] in
theorem localModule_le (hTH : (T : Subgroup G) ≤ H) : localModule T H ≤ H :=
  conjugateSpanBy_le_self ((sylowCenterSeed_le T).trans hTH)

/-- Reducedness is relative to H and its own centralizer quotient. -/
theorem localModule_reduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsPReduced 2 ((localModule T H).subgroupOf H) := by
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)
  let : IsElementaryAbelian 2 (sylowCenterSeed T) := by
    rw [sylowCenterSeed_eq]
    infer_instance
  exact reduced_conjugateSpan_of_sylow_central T H (sylowCenterSeed T) hH.1.1.2
    (sylowCenterSeed_le T) (sylowCenterSeed_centralizes T) hchar

theorem localModule_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsElementaryAbelian 2 (localModule T H) := by
  let := (localModule_reduced h hH).elementary
  have he : IsElementaryAbelian 2 (((localModule T H).subgroupOf H).map H.subtype) :=
    IsElementaryAbelian.map H.subtype
  rwa [map_subgroupOf_eq_of_le (localModule_le hH.1.1.2)] at he

theorem localModule_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H.pCoreIn 2 ≤ centralizer (localModule T H : Set G) := by
  intro q hq u hu
  obtain ⟨q,hq,rfl⟩ := hq
  exact congrArg H.subtype
    ((le_centralizer_iff.mp (localModule_reduced h hH).le_centralizer_pCore) hq
      ⟨u,localModule_le hH.1.1.2 hu⟩ hu)

/-- The embedded residual is kept separate from both local two-cores. -/
abbrev localResidual (H : Subgroup G) : Subgroup G := (pResidual 2 H).map H.subtype

theorem localResidual_supplement (hTH : (T : Subgroup G) ≤ H) :
    localResidual H ⊔ (T : Subgroup G) = H := by
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] using he

omit [Finite G] in
theorem localResidual_normalized (H : Subgroup G) :
    H ≤ normalizer (localResidual H : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

/-- V_H and V_K in 12.3.2–12.4.1 are literally equal. -/
theorem localModule_eq_residual_span (hTH : (T : Subgroup G) ≤ H) :
    localModule T H = conjugateSpanBy (sylowCenterSeed T) (localResidual H) := by
  change conjugateSpanBy (sylowCenterSeed T) H = _
  nth_rw 1 [← localResidual_supplement hTH]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (sylowCenterSeed_centralizes T)).trans (Subgroup.centralizer_le_normalizer _))
    (hTH.trans (localResidual_normalized H))

/-- The exact transport of the commutator module in the printed corollary. -/
theorem localModule_commutator_eq_residual_span (hTH : (T : Subgroup G) ≤ H) :
    ⁅localModule T H,localResidual H⁆ =
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆ := by
  rw [localModule_eq_residual_span hTH]

/-- Residual escape uses only the source omega-center centralizer guard. -/
theorem localResidual_not_centralizes_seed
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ localResidual H ≤ centralizer (sylowCenterSeed T : Set G) := by
  intro hc
  apply hH.1.2
  rw [← localResidual_supplement hH.1.1.2]
  exact sup_le (hc.trans hZ) hTM

/-- The exact source centralizer bound, including the two-closed branch. -/
theorem localModule_sylow_centralizer_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (localModule T H : Set G) = H.pCoreIn 2 := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  apply le_antisymm
  · by_cases hn : ((T : Subgroup G).subgroupOf H).Normal
    · exact inf_le_left.trans (le_pCoreIn_of_normalizes T.isPGroup' hTH
        ((normal_subgroupOf_iff_le_normalizer hTH).mp hn))
    have hp := Chapter3.HStar.minimalParabolic T hTM hH (Or.inr hn)
    obtain ⟨hTB,hBH,_⟩ := Chapter3.HStar.unique_maximal T hTM hH
    have hmin := (ChapterB.intrinsic_minimalParabolic T H
      (H ⊓ normalizer (L : Set G)) hp hTB hBH).1
    let := (localModule_reduced h hH).normal
    have hc : centralizer ((localModule T H).subgroupOf H : Set H) ≤
        ChapterB.minimalParabolicCore (T.subtype hTH) hmin := by
      apply ChapterB.minimalParabolic_normal_le_core_of_residual_not_le
      intro hk
      apply localResidual_not_centralizes_seed hTM hZ hH
      rintro _ ⟨k,hk',rfl⟩ z hz
      have hzU : z ∈ localModule T H := le_conjugateSpanBy _ _ hz
      exact congrArg H.subtype ((hk hk') ⟨z,localModule_le hTH hzU⟩ hzU)
    intro t ht
    have ht' : (⟨t,hTH ht.1⟩ : H) ∈
        ((T.subtype hTH : Sylow 2 H) : Subgroup H) ⊓
          ChapterB.minimalParabolicCore (T.subtype hTH) hmin :=
      ⟨ht.1,hc (fun u hu => Subtype.ext (ht.2 u hu))⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core] at ht'
    exact mem_map_of_mem H.subtype ht'
  · refine le_inf ?_ (localModule_core_centralizes h hH)
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh

/-- The actual H-action on all of U has trivial two-core. -/
theorem localModule_automizer_pCore_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    pCore 2 (inducedAutomizer (localModule T H) H) = ⊥ :=
  inducedAutomizer_pCore_eq_bot_of_reduced _ _ (localModule_normalized T H)
    (localModule_le hH.1.1.2) (localModule_reduced h hH)

/-- E.4.1 on the whole literal local module; no action-kernel hypothesis remains. -/
theorem localModule_parameter_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) [IsElementaryAbelian 2 (localModule T H)] :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  apply OddCore.moduleA_le_one_of_solvable
  · exact (automizerRepresentation_injective _).comp Subtype.val_injective
  · exact inducedAutomizer_isSolvable _ _ (localModule_normalized T H) hs
  · exact localModule_automizer_pCore_eq_bot h hH
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
