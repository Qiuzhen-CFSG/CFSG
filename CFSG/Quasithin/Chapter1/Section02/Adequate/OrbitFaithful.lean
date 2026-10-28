module

public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications

/-!
# Faithfulness along local chains through their Sylow orbits

The intrinsic module of a local component is nontrivial exactly when the
intrinsic module of its Sylow orbit is nontrivial. For ascent, A.4.8 compares
the component's module with its action on the two-core of that orbit; descent
is the existing conjugate-generation argument. The two orbit groups are
normalized by the Sylow subgroup, so A.4.10 applies to their inclusion.

This proves the faithful upward-closure assertion of 1.2.9(1) without using
the normalizer equality of 1.2.8(1). The stronger module comparison for the
original components remains separate.

Source: Aschbacher–Smith, A.4.8–10, pp.59–60, and 1.2.9, p.507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.Adequate
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Faithfulness ascends from a local component to its actual Sylow orbit. -/
theorem intrinsicModule_orbit_ne_bot {B T : Subgroup G}
    (hB : B ∈ L G T) (hne : intrinsicSignalizerModule B ≠ ⊥) :
    intrinsicSignalizerModule (componentOrbit B T) ≠ ⊥ := by
  let K := componentOrbit B T
  have hBK : B ≤ K := le_componentOrbit B T
  have hs : (B.subgroupOf K).IsSubnormal :=
    (hB.1.subgroupOf_of_le hBK (componentOrbit_le_sup B T)).subnormal
  have hBQ : B ≤ normalizer (K.pCoreIn 2 : Set G) :=
    hBK.trans (K.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore K))
  have hsig : IsTwoSignalizer B K (K.pCoreIn 2) :=
    (isTwoSignalizer_iff _ _ _).mpr ⟨pCoreIn_le _ _, isPGroup_pCoreIn _ _, hBQ⟩
  have hcomm := signalizer_commutator_le_pCore B K (K.pCoreIn 2)
    hBK hs (mem_L_isPPerfect hB) hsig
  have hdetect := signalizerModule_ne_bot_iff_intrinsic B (K.pCoreIn 2)
    (mem_L_isPPerfect hB) (isPGroup_pCoreIn _ _) hBQ
    (pCoreAmbient_mono_of_isSubnormalIn B K 2 hBK hs) hcomm
  have hle : signalizerModule B (K.pCoreIn 2) ≤ intrinsicSignalizerModule K := by
    change signalizerModule B (K.pCoreIn 2) ≤ signalizerModule K (K.pCoreIn 2)
    rw [signalizerModule_eq_commutator_omegaCenter, signalizerModule_eq_commutator_omegaCenter]
    exact commutator_mono hBK le_rfl
  intro hz
  exact (hdetect.mpr hne) (eq_bot_iff.mpr (hle.trans hz.le))

/-- The faithful local family is upward closed, without a component-normalizer
premise or a chosen invariant module. -/
theorem faithful_local_overgroup (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {B K : Subgroup G} (hB : B ∈ MainForward.faithfulLocalComponents T)
    (hK : K ∈ L G T) (hBK : B ≤ K) :
    K ∈ MainForward.faithfulLocalComponents T := by
  have hb := (mem_faithfulLocalComponents_iff T B).mp hB
  let X := componentOrbit B (T : Subgroup G)
  let Y := componentOrbit K (T : Subgroup G)
  have h114 := lemma_1_1_4_6 T hE
  have hX := (Terminal.local_component_and_orbit_signalizerType T h114 hb.1).2
  have hY := (Terminal.local_component_and_orbit_signalizerType T h114 hK).2
  have hXY : X ≤ Y := iSup_mono fun _ => map_mono hBK
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := le_normalizer_componentOrbit B T
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := le_normalizer_componentOrbit K T
  have hSyl : IsSylowIn 2 (T : Subgroup G) (Y ⊔ (T : Subgroup G)) := by
    refine ⟨T.subtype le_sup_right, ?_⟩
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  have hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨P, hP⟩ := hSyl
    exact (pCoreIn_le_sylow _ P).trans_eq hP
  have hSylN : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (X : Set G))
      ((Y ⊔ (T : Subgroup G)) ⊓ normalizer (X : Set G)) := by
    rw [inf_of_le_left hTX]
    exact hSyl.restrict (le_inf le_sup_right hTX) inf_le_left
  have hfX : IsFaithfulSignalizerType X := ⟨hX, intrinsicModule_orbit_ne_bot hb.1 hb.2.2⟩
  have hfY := (SourceChains.source_A410 X Y T hXY hX hY hTY hSyl
    (le_inf hcore (hcore.trans hTX)) hSylN).2.2 hfX
  exact (mem_faithfulLocalComponents_iff T K).mpr
    ⟨hK, mem_L_isSignalizerType T hE hK,
      Terminal.intrinsicModule_ne_bot_of_orbit hK hfY.2⟩

end CFSG.Quasithin.Chapter1.Section02.Adequate
