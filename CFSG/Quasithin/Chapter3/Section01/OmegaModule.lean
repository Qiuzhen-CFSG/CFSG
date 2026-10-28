module

public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import CFSG.Quasithin.Chapter3.Section01.CenterAlternative
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The original omega-center module in the Baumann branch

For every H in the original qrc configuration, characteristic two and
B.2.14 make U=⟨Ω₁(Z(T))ᴴ⟩ reduced in H. The subgroup and the Sylow
embedding are transported literally. If H does not centralize the
Sylow omega-center, its two-residual moves U: otherwise the residual
and the Sylow supplement both centralize that seed.

These construct the module and the residual movement used in source 3.1.7;
the E.2.3 natural-factor and Sylow alternatives remain a separate proof.
Source: Aschbacher–Smith, Lemma 3.1.7, combined manuscript
of 1 March 2004, printed pp.575–576.
-/

public section
open Subgroup


namespace CFSG.Quasithin.Chapter3
open Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sylowOmega_reduced
    (h : QrcHypotheses T M M₀ H V)
    (hE : IsEvenCharacteristicAt T) :
    IsPReduced 2 ((conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) := by
  have hTH : (T : Subgroup G) ≤ H := h.right_mem.1.1.2
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T hE h.right_mem.1.1)
  let S : Sylow 2 H := T.subtype hTH
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (S : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hTH)]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hr := omegaCenter_normalClosure_reduced S hchar
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hTH)] at hr
  exact hr

end CFSG.Quasithin.Chapter3

namespace CFSG.Quasithin.Chapter3
open Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.residual_moves_sylowOmega
    (h : QrcHypotheses T M M₀ H V)
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    ¬ (pResidual 2 H).map H.subtype ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G) := by
  intro hc
  have hTH : (T : Subgroup G) ≤ H := h.right_mem.1.1.2
  let S : Sylow 2 H := T.subtype hTH
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top S)
  change (pResidual 2 H ⊔ (S : Subgroup H)).map H.subtype = (⊤ : Subgroup H).map H.subtype at he
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTH
  rw [hS] at he
  apply hZ
  intro z hz
  have hzT : z ∈ (T : Subgroup G) := ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hcent : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    rw [← he]
    refine sup_le (hc.trans (centralizer_le (le_conjugateSpanBy _ _))) ?_
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  refine ⟨⟨z, hTH hzT⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  exact Subtype.ext ((hcent y.property) z hz).symm

end CFSG.Quasithin.Chapter3
