module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Source
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Faithful signalizers detected by the original plus kernel

The original fixed layer U0 is contained in Ω₁Z(QH). A nontrivial
subnormal two-perfect K in the plus kernel moves U0. The A.4.8 module
comparison carries that movement into the intrinsic module V(K), while
characteristic-two inheritance gives F*(K)=O₂(K). Thus K belongs to the
actual source family X_f. No intrinsic-module or faithful-action premise
is assumed. Source: 13.7.4(1), calculation (!) on printed p.937.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open ChapterA.Section04 ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

include h

theorem fixedLayer_le_omegaCenter (hE : IsElementaryAbelian 2 D.UH) :
    fixedLayer D ≤ Stellmacher.omegaOneCenterAmbient D.QH := by
  let := hE
  intro x hx
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff D.QH x).mpr
    ⟨h.UH_le_QH hx.1, elemPow_eq_one_of_isElementaryAbelian x hx.1, hx.2⟩

/-- The actual X_f membership required immediately after (!) in13.7.4. -/
theorem subnormal_kernel_faithful_signalizer (hE : IsElementaryAbelian 2 D.UH)
    {K : Subgroup G} (hKC : K ≤ kernel D)
    (hn : (K.subgroupOf D.H).IsSubnormal) (hp : IsPPerfect 2 K) (hne : K ≠ ⊥) :
    IsFaithfulSignalizerType K := by
  have hKH : K ≤ D.H := hKC.trans kernel_le_H
  have hHQ := Hypothesis.H_normalizes_QH (D := D)
  have hQK := core_normalizes_subnormal hKH hn hp
  have hcore := subnormal_core_le hKH hn
  have hc := commutator_le_pCore_of_mutual_normalization K D.QH
    (isPGroup_pCoreIn 2 D.H) (hKH.trans hHQ) hQK
  have hmove := (subnormal_kernel_structure h hKC hn hp hne).2.1
  have hle : ⁅fixedLayer D, K⁆ ≤ intrinsicSignalizerModule K := by
    rw [commutator_comm]
    apply (commutator_mono le_rfl (fixedLayer_le_omegaCenter h hE)).trans
    rw [← signalizerModule_eq_commutator_omegaCenter]
    exact signalizerModule_le_intrinsicModule K D.QH hp (hKH.trans hHQ) hcore hc
  have hHe : D.H ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (by
    simpa only [h.characteristic_H] using Theory.GroupTheory.centralizer_generalizedFitting_le D.H)
  have hKe := Chapter1.lemma_1_1_3_1 hHe hne hKH hn
  exact ⟨⟨hne, hp, Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp hKe)⟩, fun hz => hmove (le_bot_iff.mp (hle.trans hz.le))⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

include d

/-- Source13.7.4 applies the intrinsic X_f theorem to the original natural
setup and any actual subnormal two-perfect subgroup of the plus kernel. -/
theorem source_plus_kernel_faithful_signalizer
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {K : Subgroup G}
    (hK : K ≤ PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hn : (K.subgroupOf H).IsSubnormal) (hp : IsPPerfect 2 K) (hne : K ≠ ⊥) :
    ChapterA.Section04.IsFaithfulSignalizerType K := by
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  exact PlusAction.subnormal_kernel_faithful_signalizer h
    (conjugateSpanBy_elementary_of_commutative V₃ H) hK hn hp hne

end CFSG.Quasithin.Chapter13.Section07
