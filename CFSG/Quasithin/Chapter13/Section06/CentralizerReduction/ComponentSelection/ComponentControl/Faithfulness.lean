module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal

/-!
# Detecting faithfulness of the containing component

In a characteristic-two overgroup of T, a central involution of T lies in
the omega-center of the overgroup's two-core. A component moving that
involution has nontrivial signalizer module there. The checked A.4.8 comparison
then makes its intrinsic module nontrivial, establishing membership in the
actual L_f(G,T).

This discharges the faithful-family step in Aschbacher–Smith, Lemma 13.6.16(1),
combined 1 March 2004 manuscript, printed p.930, using Definition A.4.7 and
the A.4.9 argument on printed p.60.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ChapterA.Section04 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]

/-- A moving C-component of a local Sylow overgroup lies in the genuine
faithful family. Characteristic two places the central involution in the
omega-center of the overgroup's core, then A.4.8 detects the intrinsic module. -/
theorem faithful_of_moving_cComponent
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (M K : Subgroup G) (hM : M ∈ Chapter1.HOver G (T : Set G))
    (hK : K ∈ Chapter1.cComponentsIn M)
    (hnc : ¬ K ≤ centralizer ({z} : Set G)) :
    K ∈ MainForward.faithfulLocalComponents T := by
  have hL : K ∈ Chapter1.L G (T : Subgroup G) := (Chapter1.lemma_1_2_6 T hM).1 hK |>.2
  have hHe := Chapter1.lemma_1_1_4_6 T hE hM
  have hTM : (T : Subgroup G) ≤ M := hM.2
  let Q := M.pCoreIn 2
  have hQT : Q ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  obtain ⟨hzT, hz2, hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzQ : z ∈ Q := by
    let zm : M := ⟨z, hTM hzT⟩
    have hc : zm ∈ centralizer (pCore 2 M : Set M) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      apply Subtype.ext
      exact hzC (x : G) (hQT (mem_map.mpr ⟨x, hx, rfl⟩))
    exact mem_map.mpr ⟨zm, Chapter1.mem_He_iff.mp hHe hc, rfl⟩
  have hzW : z ∈ omegaOneCenterAmbient Q :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzQ, hz2, fun x hx => hzC x (hQT hx)⟩
  have hMQ : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore M)
  have hKQ : K ≤ normalizer (Q : Set G) := hK.1.trans hMQ
  have hX := mem_L_isPPerfect hL
  have hsig : IsTwoSignalizer K M Q :=
    (isTwoSignalizer_iff _ _ _).mpr ⟨pCoreIn_le 2 M, isPGroup_pCoreIn 2 M, hKQ⟩
  have hcomm := signalizer_commutator_le_pCore K M Q hK.1 hK.2.subnormal hX hsig
  have hcore : K.pCoreIn 2 ≤ Q :=
    pCoreAmbient_mono_of_isSubnormalIn K M 2 hK.1 hK.2.subnormal
  have hmove : signalizerModule K Q ≠ ⊥ := by
    intro he
    have hcent := commutator_eq_bot_iff_le_centralizer.mp
      ((signalizerModule_eq_commutator_omegaCenter K Q).symm.trans he)
    apply hnc
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp (hcent hk) z hzW).symm
  exact (mem_faithfulLocalComponents_iff_module T hE).mpr
    ⟨hL, (signalizerModule_ne_bot_iff_intrinsic K Q hX
      (isPGroup_pCoreIn 2 M) hKQ hcore hcomm).mp hmove⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
