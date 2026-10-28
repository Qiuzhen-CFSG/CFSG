module

public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Core
import Theory.GroupTheory.TwoLocalTransport
/-!
# Sylow transport in the unique maximal two-local case

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 2.3.3, 2.3.7 and 2.3.8, printed pp.522–524.
A subgroup with nontrivial two-core lies in a maximal two-local. If it
contains a Sylow subgroup of M, conjugacy inside M carries that Sylow
to T; uniqueness at T forces the whole subgroup into M. Thus members
of Γ have strictly smaller two-part than M. Since the orders are powers
of two, doubling the smaller order is still at most the order of T.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

theorem core_overgroup_le_of_sylow (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : twoCore H ≠ ⊥) (P : Sylow 2 M)
    (hPH : (P : Subgroup M).map M.subtype ≤ H) : H ≤ M := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P (T.subtype hTM)
  let f := (MulAut.conj (m : G)).toMonoidHom
  have hconj : ((P : Subgroup M).map M.subtype).map f = (T : Subgroup G) := by
    have hh := congrArg (fun R : Sylow 2 M => (R : Subgroup M).map M.subtype) hm
    change ((P : Subgroup M).map (MulAut.conj m).toMonoidHom).map M.subtype = _ at hh
    rw [map_map] at hh
    change (P : Subgroup M).map (f.comp M.subtype) = _ at hh
    simpa only [← map_map, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hh
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    apply hH
    simp only [twoCore, he, Subgroup.map_bot]
  obtain ⟨L, hL, hHL⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  have hLf := Theory.GroupTheory.isTwoLocal_map (MulAut.conj (m : G)) hL.1
  obtain ⟨K, hLK, hK⟩ := Finite.exists_le_maximal hLf
  have hTK : (T : Subgroup G) ≤ K :=
    hconj ▸ (map_mono (hPH.trans hHL) (f := f)).trans hLK
  have hKM := hunique K hK hTK
  have hMM : M.map f = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  apply (map_le_map_iff_of_injective (f := f) (MulAut.conj (m : G)).injective).mp
  rw [hMM]
  exact (map_mono hHL).trans (hKM ▸ hLK)

theorem twoPart_lt_of_beta_core (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {U : Subgroup G} (hU : U ∈ beta M) (hUH : U ≤ H)
    (hH : twoCore H ≠ ⊥) (hHM : ¬ H ≤ M) : twoPart H < twoPart M := by
  obtain ⟨S, _, hS⟩ := beta_exists_sylow hU hUH
  have hc : twoPart H ≤ twoPart M := by
    rw [← sylow_image_card H S]
    exact beta_card_le_twoPart hS hS.2.1
  apply lt_of_le_of_ne hc
  intro he
  obtain ⟨P, hP⟩ := exists_sylow_of_card hS.2.1 ((sylow_image_card H S).trans he)
  exact hHM (core_overgroup_le_of_sylow T hTM hunique hH P
    (hP ▸ map_subtype_le _))

theorem twoPart_eq_sylow_card (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    twoPart M = Nat.card (T : Subgroup G) := by
  have hc := sylow_image_card M (T.subtype hTM)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hc.symm

theorem gamma_twoPart_lt (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {E : Set (Subgroup G)} (hH : H ∈ gamma E M) :
    twoPart H < twoPart M := by
  obtain ⟨P, hP, hPH⟩ := hH.2
  exact twoPart_lt_of_beta_core T hTM hunique hP.1
    (hP.2.2.2.1.trans hPH) hH.1 (gamma_not_le hH)

theorem gamma_twoPart_double_le (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {E : Set (Subgroup G)} (hH : H ∈ gamma E M) :
    2 * twoPart H ≤ Nat.card (T : Subgroup G) := by
  have hh := gamma_twoPart_lt T hTM hunique hH
  rw [twoPart, twoPart] at hh
  have hn := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh
  rw [← twoPart_eq_sylow_card T hTM]
  change 2 * 2 ^ (Nat.card H).factorization 2 ≤ 2 ^ (Nat.card M).factorization 2
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by decide) hn
end CFSG.Quasithin.Chapter2
