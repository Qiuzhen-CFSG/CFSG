module

public import Theory.GroupTheory.ElementaryThompsonUniqueMaximal
public import CFSG.Quasithin.Chapter3.Section01.OmegaModule
public import CFSG.Quasithin.Chapter3.Section01.OffenderBranch

/-!
# Thompson movement on the original omega-center orbit

In the noncentral branch of 3.1.7, uniqueness excludes J(T) being normal
in H. The unique-maximal/Frattini argument proves J(T) moves the actual
orbit U=⟨Ω₁(Z(T))ᴴ⟩. B.2.14 makes U reduced, elementary, and contained
in T, so its literal faithful internal conjugation action is an FF-module.

Together these discharge the module and movement hypotheses of E.2.3.
Its natural-factor classification and Baumann Sylow conclusions remain
the distinct source step needed to finish 3.1.7.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 3.1.7, printed pp.575–576.
-/

public section
namespace CFSG.Quasithin.Chapter3
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.thompson_moves_sylowOmega
    (h : QrcHypotheses T M M₀ H V)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := h.right_mem.1.1.2
  let S : Sylow 2 H := T.subtype hTH
  let Z := omegaOneCenterAmbient (S : Subgroup H)
  let U := normalClosure (Z : Set H)
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hzmap : Z.map H.subtype = omegaOneCenterAmbient (T : Subgroup G) := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hz : Z = (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hzmap, map_subgroupOf_eq_of_le (hZT.trans hTH)]
  have hU : U = (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H := by
    change normalClosure (Z : Set H) = _
    rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hTH)]
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hJn : ¬ (elementaryAbelianMaxJ (S : Subgroup H)).Normal := by
    intro hn
    let := hn
    have hnorm := (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hjmap] at hnorm
    exact h.no_common_normal hu (h.common_normal_of_thompson_normal hM hJ hnorm)
  have huS : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤ := by
    obtain ⟨B, ⟨hBc, hBT⟩, hb⟩ := HStar.unique_maximal_subgroup T
      (h.sylow_le.trans h.left_le) h.right_mem
    have hSB : (S : Subgroup H) ≤ B := by
      intro s hs
      obtain ⟨b, hb, he⟩ := hBT hs
      exact H.subtype_injective he ▸ hb
    refine ⟨hSB.trans_lt hBc.lt_top, B, ⟨hSB, hBc.covBy_top⟩, ?_⟩
    intro C hC
    apply hb C
    refine ⟨hC.2.isCoatom, ?_⟩
    intro t ht
    exact ⟨⟨t, hTH ht⟩, hC.1 ht, rfl⟩
  have hnot := thompson_not_centralizes_of_unique_maximal S U Z le_normalClosure
    (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
    (fun hz => hZ (by rw [← hzmap]; exact map_mono hz)) huS hJn
  intro hc
  apply hnot
  intro j hj u hu
  apply Subtype.ext
  have hj' : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
    hjmap ▸ mem_map_of_mem H.subtype hj
  have hu' : (u : G) ∈ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H := by
    change u ∈ (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    exact hU ▸ hu
  exact hc hj' u hu'

end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sylowOmega_elementary
    (h : QrcHypotheses T M M₀ H V) (hE : IsEvenCharacteristicAt T) :
    IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hUH : U ≤ H := conjugateSpanBy_le
    (fun z hz => h.right_mem.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    H.le_normalizer
  let := (h.sylowOmega_reduced hE).elementary
  have he : IsElementaryAbelian 2 ((U.subgroupOf H).map H.subtype) := IsElementaryAbelian.map _
  rwa [map_subgroupOf_eq_of_le hUH] at he

theorem QrcHypotheses.sylowOmega_le_sylow
    (h : QrcHypotheses T M M₀ H V) (hE : IsEvenCharacteristicAt T) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤ (T : Subgroup G) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hTH : (T : Subgroup G) ≤ H := h.right_mem.1.1.2
  have hUH : U ≤ H := conjugateSpanBy_le
    (fun z hz => hTH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) H.le_normalizer
  have hcore := map_mono (f := H.subtype) (h.sylowOmega_reduced hE).le_pCore
  rw [map_subgroupOf_eq_of_le hUH] at hcore
  have hRT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  exact hcore.trans hRT

/-- The original omega-orbit is the FF-module required by the noncentral E.2.3 application. -/
theorem QrcHypotheses.sylowOmega_isFF
    (h : QrcHypotheses T M M₀ H V) (hE : IsEvenCharacteristicAt T)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    letI := h.sylowOmega_elementary hE
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation H
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
        (le_normalizer_conjugateSpanBy _ H)) := by
  let := h.sylowOmega_elementary hE
  exact internalActionImage_isFFModule_of_thompson_not_le T H _ h.right_mem.1.1.2
    (h.sylowOmega_le_sylow hE) (le_normalizer_conjugateSpanBy _ H)
    (h.thompson_moves_sylowOmega hM hu hJ hZ)

end CFSG.Quasithin.Chapter3
