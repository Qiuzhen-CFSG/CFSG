module
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SelfCentralizingCore
import Mathlib.Tactic
/-!
# Odd cores and ordinary components under genuine C.2.8

The original C-component makes its conjugate span perfect. The actual
commutator-generated elementary module therefore centralizes O(H) by
A.1.26. Its normalizer bound puts O(H) inside M, whose characteristic-two
condition forces that odd core to be trivial. The same condition excludes
every ordinary component of H from M. No component or catalogue row is
selected in advance.

Source: Aschbacher–Smith, C.2.9(1) and C.2.10(1–2), printed pp.147–148.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

omit [Finite G] in
/-- Perfection is inherited from the actual source component and its conjugate span. -/
theorem span_perfect (h : HypothesisC28 κ H M L R V) :
    Group.IsPerfect (conjugateSpanBy L M) := by
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  exact conjugateSpanBy_isPerfect L M

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem oddCore_eq_bot_of_module {A : Type*} [Group A] [Finite A]
    (hsqt : IsStronglyQuasithin A) (M X V : Subgroup A)
    (hf : generalizedFitting M = pCore 2 M) [Group.IsPerfect X]
    [IsElementaryAbelian 2 V] (hVX : V = ⁅V,X⁆)
    (hN : normalizer (V : Set A) ≤ M) : pPrimeCore 2 A = ⊥ := by
  have hcomm := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqt X V
    perfect_twoPerfect hVX.symm
  have hOM : pPrimeCore 2 A ≤ M :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)).trans hN
  have hMf : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    simpa only [hf] using centralizer_generalizedFitting_le M
  have hMo := pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hMf
  have hc : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 A).subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOM).toEquiv]
    exact pPrimeCore_coprime_card
  have he := pPrimeCore_eq_bot_iff.mp hMo ((pPrimeCore 2 A).subgroupOf M)
    inferInstance hc
  have hm := congrArg (map M.subtype) he
  simpa only [map_subgroupOf_eq_of_le hOM,Subgroup.map_bot] using hm

/-- C.2.10(1): the original H has trivial odd core. -/
theorem oddCore_eq_bot (h : HypothesisC28 κ H M L R V) : pPrimeCore 2 H = ⊥ := by
  let X := conjugateSpanBy L M
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hVH : V ≤ H := h.module_le.trans hXH
  let := h.span_perfect
  let : Group.IsPerfect (X.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let := h.module_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  have hVX : V.subgroupOf H = ⁅V.subgroupOf H,X.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hXH]
    exact h.module_commutator
  have hN : normalizer (V.subgroupOf H : Set H) ≤ M.subgroupOf H := by
    rw [← subgroupOf_normalizer_eq hVH]
    intro x hx
    exact h.module_normalizer ⟨x.property,hx⟩
  have hf : generalizedFitting (M.subgroupOf H) = pCore 2 (M.subgroupOf H) := by
    let e := subgroupOfEquivOfLe h.local_le
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,h.local_fitting]
  exact oddCore_eq_bot_of_module h.sqtk.stronglyQuasithin (M.subgroupOf H)
    (X.subgroupOf H) (V.subgroupOf H) hf hVX hN

/-- C.2.10(2): every actual ordinary component of H escapes the local M. -/
theorem component_not_le (h : HypothesisC28 κ H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) : ¬ K ≤ M.subgroupOf H := by
  intro hk
  have hc := hK.subgroupOf hk
  let : IsQuasisimple (K.subgroupOf (M.subgroupOf H)) := hc.2
  have hq := component_le_generalizedFitting (M.subgroupOf H) _ hc
  let e := subgroupOfEquivOfLe h.local_le
  have hf : generalizedFitting (M.subgroupOf H) = pCore 2 (M.subgroupOf H) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,h.local_fitting]
  rw [hf] at hq
  have hp := pCore_isPGroup.to_le hq
  let : IsSimpleGroup ((K.subgroupOf (M.subgroupOf H)) ⧸ center (K.subgroupOf (M.subgroupOf H))) :=
    IsQuasisimple.simple
  let : Nontrivial (K.subgroupOf (M.subgroupOf H)) :=
    (QuotientGroup.mk'_surjective (center (K.subgroupOf (M.subgroupOf H)))).nontrivial
  exact Group.IsPerfect.not_isNilpotent (K.subgroupOf (M.subgroupOf H)) hp.isNilpotent
end CFSG.Quasithin.ChapterC.HypothesisC28
