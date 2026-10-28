module

public import CFSG.Quasithin.Chapter3.Section01.E23Input
public import CFSG.Quasithin.ChapterB.Section02.BaumannFrattini
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original outside omega-center action in 13.2.7

The elementary orbit U = ⟨Ω₁(Z(T))ᴴ⟩ is reduced in the original H by
characteristic two. If J(T) centralized U, the centralizing Baumann
Frattini argument would generate H from C_H(U) and N_H(Baum(T)). The
first factor is in M by minimality of H and the noncentral seed; the
second is in M by the genuine earlier 5.1.7(1). This contradiction
constructs Thompson movement, and hence all intrinsic E.2.3 hypotheses.

Source: Aschbacher–Smith 13.2.7–8, printed p.880, using 5.1.7(1),
B.2.14 and E.2.3. The Baumann-normalizer bound remains an earlier source
premise; no solvability or module-classification conclusion is assumed.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
universe u
variable {G : Type u} [Group G] [Finite G]

noncomputable abbrev omegaOrbit (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H

omit [Finite G] in
private theorem omega_le (T : Sylow 2 G) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
  fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1

omit [Finite G] in
private theorem orbit_le (T : Sylow 2 G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) : omegaOrbit T H ≤ H :=
  conjugateSpanBy_le ((omega_le T).trans hTH) H.le_normalizer

/-- Reducedness holds before applying any action classification. -/
theorem omegaOrbit_reduced {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    IsPReduced 2 ((omegaOrbit T H).subgroupOf H) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hz : omegaOneCenterAmbient (S : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le ((omega_le T).trans hTH)]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1)
  have hr := omegaCenter_normalClosure_reduced S hc
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ H ((omega_le T).trans hTH)] at hr
  exact hr

/-- The genuine earlier Baumann bound forces the original Thompson movement. -/
theorem thompson_moves_omegaOrbit {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (omegaOrbit T H : Set G) := by
  intro hJ
  let U := omegaOrbit T H
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hUH : U ≤ H := orbit_le T hTH
  have hU := omegaOrbit_reduced hG T hH
  let := hU.normal
  let := hU.elementary
  have he : IsElementaryAbelian 2 U := by
    have hm : IsElementaryAbelian 2 (((U.subgroupOf H).map H.subtype)) :=
      IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hUH] at hm
  let := he
  have hf := ChapterB.BaumannFrattini.centralizing_characteristic_factorization
    T H U hTH hUH (le_inf ((sSup_le fun _ hA => hA.1).trans hTH) hJ)
    (⊤ : Subgroup (ChapterB.baumann (T : Subgroup G)))
  rw [← MonoidHom.range_eq_map, range_subtype] at hf
  have hCT : (H ⊓ centralizer (U : Set G)) ⊔ (T : Subgroup G) < H := by
    apply lt_of_le_of_ne (sup_le inf_le_left hTH)
    intro heq
    apply hZ
    rw [← heq]
    apply sup_le
    · exact inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _))
    · intro t ht z hz
      exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hCM : H ⊓ centralizer (U : Set G) ≤ M := le_sup_left.trans
    (Chapter3.HStar.proper_overgroup_le T hH le_sup_right hCT)
  exact hH.1.2 (hf.le.trans (sup_le hCM (inf_le_right.trans hB)))

/-- All E.2.3 source hypotheses on the literal H and its original omega orbit. -/
theorem e23_hypotheses {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    IsSQTK κ H ∧ generalizedFitting H = pCore 2 H ∧
      ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ ∧
      IsPReduced 2 ((omegaOrbit T H).subgroupOf H) ∧
      ¬ elementaryAbelianMaxJ
          ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤
        centralizer ((omegaOrbit T H).subgroupOf H : Set H) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hp := Chapter3.HStar.minimalParabolic T hTM hH
    (Or.inl ((normalizer_le_normalizer_baumann _).trans hB))
  have hpi : ChapterB.IsMinimalParabolicOver (T.subtype hTH) ⊤ := by
    apply (ChapterB.isMinimalParabolicOver_top_iff _).mpr
    refine ⟨?_, ((ChapterB.isMinimalParabolicOver_iff T H).mp hp).2⟩
    obtain ⟨B, ⟨hBc,hBT⟩, hb⟩ := Chapter3.HStar.unique_maximal_subgroup T hTM hH
    have hSB : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤ B := by
      intro s hs
      obtain ⟨b,hb,he⟩ := hBT hs
      exact H.subtype_injective he ▸ hb
    refine ⟨B,⟨hBc,hSB⟩,?_⟩
    intro C hC
    apply hb C
    exact ⟨hC.1,fun t ht => ⟨⟨t,hTH ht⟩,hC.2 ht,rfl⟩⟩
  refine ⟨Chapter3.sqtk_of_mem_H hG hH.1.1.1,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1)),
    hpi,omegaOrbit_reduced hG T hH,?_⟩
  intro hc
  apply thompson_moves_omegaOrbit hG T hH hB hZ
  have hjmap : (elementaryAbelianMaxJ
      ((T.subtype hTH : Sylow 2 H) : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  rw [← hjmap]
  rintro g ⟨j,hj,rfl⟩ z hz
  exact congrArg H.subtype (hc hj ⟨z,orbit_le T hTH hz⟩ hz)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
