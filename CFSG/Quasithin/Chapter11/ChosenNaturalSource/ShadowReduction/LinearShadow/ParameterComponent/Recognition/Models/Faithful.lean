module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Seed
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful

/-!
# The faithful maximal overcomponent in the original recognition argument

The omega-center of the prescribed Sylow lies in Ω₁Z(O₂(H)). Its movement
by the selected C-component makes the corresponding signalizer module
nontrivial. The A.4.8 comparison transfers this to the component's own
intrinsic module, proving membership in the genuine faithful local family.
Finite maximality and the proved 1.2.9 upward closure then construct a
faithful maximal overcomponent. It still escapes N_G(L) and moves the
same omega-center. The source application constructs the seed as well.

These are the actual subgroups needed before applying A.3.12 and the
FF-module exclusions; neither an embedding classification nor existence
of an FF-module is assumed. Recognition/Models combines this construction
with the numerical model sieve. The remaining recognition proof stays
with the parameter-component owner, and preceding-source discharge with
the linear-geometry owner.
Source: Aschbacher--Smith 11.3.5(1), pp.771–772; 1.2.9, p.507;
A.4.8–10, pp.59–60.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Omega-center movement proves faithfulness of the actual seed component. -/
theorem ComponentSeed.faithful (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) :
    K ∈ MainForward.faithfulLocalComponents T := by
  have hlocal := s.mem_local_family h
  have hperf := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  have hKH := s.component.1
  have hsub := s.component.2.subnormal
  let R := H.pCoreIn 2
  have hR : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype h.outside.1.1.2)
    change R ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le h.outside.1.1.2] at hh
  have hKR : K ≤ normalizer (R : Set G) :=
    hKH.trans (H.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore H))
  have hcore : K.pCoreIn 2 ≤ R :=
    pCoreAmbient_mono_of_isSubnormalIn K H 2 hKH hsub
  have hsig : IsTwoSignalizer K H R :=
    (isTwoSignalizer_iff _ _ _).mpr ⟨pCoreIn_le 2 H,isPGroup_pCoreIn 2 H,hKR⟩
  have hcomm : ⁅K,R⁆ ≤ K.pCoreIn 2 :=
    signalizer_commutator_le_pCore K H R hKH hsub hperf hsig
  have hZcore : sourceZ T ≤ R := by
    have hi := map_mono (f := H.subtype) (omegaOrbit_reduced h).le_pCore
    rw [map_subgroupOf_eq_of_le (omegaOrbit_le h.outside.1.1.2)] at hi
    exact (le_conjugateSpanBy (sourceZ T) H).trans hi
  have hZ : sourceZ T ≤ omegaOneCenterAmbient R := by
    intro z hz
    obtain ⟨hzT,hzC,hz2⟩ := (mem_omegaCenterIn_iff (T : Subgroup G) z).mp hz
    exact (mem_omegaOneCenterAmbient_iff R z).mpr
      ⟨hZcore hz,hz2,fun r hr => mem_centralizer_iff.mp hzC r (hR hr)⟩
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (S.source.simpleQTKE.evenCharacteristic T)).mpr
  refine ⟨hlocal,(signalizerModule_ne_bot_iff_intrinsic K R hperf
    (isPGroup_pCoreIn 2 H) hKR hcore hcomm).mp ?_⟩
  intro he
  apply s.moves_omega_center h
  apply le_bot_iff.mp
  calc
    ⁅sourceZ T,K⁆ ≤ signalizerModule K R := by
      rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm (sourceZ T) K]
      exact commutator_mono le_rfl hZ
    _ ≤ ⊥ := he.le

/-- Construct a faithful maximal overcomponent, retaining escape and movement. -/
theorem ComponentSeed.exists_faithful_maximal_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) :
    ∃ J : Subgroup G, K ≤ J ∧ J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ := by
  obtain ⟨J,hJ,hKJ⟩ := Chapter1.exists_mem_LStar_ge (s.mem_local_family h)
  refine ⟨J,hKJ,hJ,Chapter1.Section02.Adequate.faithful_local_overgroup T
    (S.source.simpleQTKE.evenCharacteristic T) (s.faithful h) hJ.1 hKJ,
    fun he => s.outside h (hKJ.trans he),?_⟩
  intro he
  exact s.moves_omega_center h (le_bot_iff.mp ((commutator_mono le_rfl hKJ).trans he.le))

/-- The original counterexample supplies both the seed and its faithful
maximal overcomponent, without either subgroup as an input. -/
theorem exists_componentSeed_with_faithful_maximal
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ := by
  obtain ⟨K,s⟩ := exists_componentSeed h pr hc hs
  obtain ⟨J,hKJ,hJ,hf,ho,hm⟩ := s.exists_faithful_maximal_overcomponent h
  exact ⟨K,J,s,hKJ,hJ,hf,ho,hm⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
