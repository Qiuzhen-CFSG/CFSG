module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.GroupTheory.PResidual.RelativeCoreCommutator

/-!
# Nonfaithful local components in the original A₅ context

Original 13.3.1(4) identifies the two-core quotient of every faithful local
component with A₅. A local component whose literal quotient is not A₅
therefore has zero intrinsic signalizer module and centralizes the omega
center of its own two-core. Its subnormality in the actual Sylow join and
the A.4.8 comparison give centralization of that join's core omega-center
as well. Sylow normalization of the component is not required.

Source: Aschbacher--Smith, Hypothesis 13.3.1(4), printed p.884, and
A.4.2(2), A.4.8(4), printed pp.57,59--60, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter1.Section02.Adequate ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ I : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hI : I ∈ Chapter1.L G (T : Subgroup G))
  (hnot : ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)))
include d hI hnot

/-- The original uniform A₅ clause forces a non-A₅ local component to be
nonfaithful, with the intrinsic module of the same subgroup retained. -/
theorem nonfive_local_intrinsicModule_eq_bot : intrinsicSignalizerModule I = ⊥ := by
  by_contra hne
  exact hnot (d.uniform_A5 I ((mem_faithfulLocalComponents_iff_module T
    (d.hypothesis.qtke.evenCharacteristic T)).mpr ⟨hI,hne⟩))

/-- The component centralizes the omega-center of its actual intrinsic core. -/
theorem nonfive_local_centralizes_core_omegaCenter :
    I ≤ centralizer (omegaOneCenterAmbient (I.pCoreIn 2) : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← signalizerModule_eq_commutator_omegaCenter]
  exact d.nonfive_local_intrinsicModule_eq_bot hI hnot

/-- Subnormality and A.4.8 transfer centralization to the entire two-core
of the original Sylow join, without assuming that the Sylow normalizes I. -/
theorem nonfive_local_centralizes_join_core_omegaCenter :
    I ≤ centralizer (omegaOneCenterAmbient
      ((I ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) := by
  let J := I ⊔ (T : Subgroup G)
  have hp : IsPPerfect 2 I := mem_L_isPPerfect hI
  have hn : I ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (show I ≤ J from le_sup_left).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hcore : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn I J 2 le_sup_left hI.1.subnormal
  have hc : ⁅I,J.pCoreIn 2⁆ ≤ I.pCoreIn 2 := by
    rw [commutator_comm I]
    exact (commutator_pCoreIn_eq_intrinsic_of_subnormal I J le_sup_left
      hI.1.subnormal hp).le.trans (le_normalizer_iff_commutator_le_left.mp
        (I.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore I)))
  have hm := signalizerModule_le_intrinsicModule I (J.pCoreIn 2) hp hn hcore hc
  rw [d.nonfive_local_intrinsicModule_eq_bot hI hnot] at hm
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← signalizerModule_eq_commutator_omegaCenter]
  exact bot_unique hm

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
