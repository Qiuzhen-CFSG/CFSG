module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lifting E-generation across a normal subgroup of prime order

A positive E-generation bound for G/N lifts when N has prime order.
Quotient lifting first gives generation modulo N. If N is a two-group,
it lies in the Sylow subgroup and hence the weak-closure normalizer.
Otherwise E.1.10(6) puts each commutator [N,A] in the generated subgroup.
The prime-order intersection dichotomy either absorbs N directly or forces
N to centralize the weak closure, which also absorbs N.

This argument retains the corrected local tau through the imported lifting
and odd-commutator theorems. The Janko-four centralizer application removes
the actual order-three covering kernel before lifting through its two-core.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.10(6)--(7), printed pp.211--212, and E.1.14(5), p.214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- A normal prime-order kernel preserves every positive E-generation bound. -/
theorem IsEGenerated.of_normal_prime_order {i p : ℕ} (hi : 1 ≤ i)
    [Fact p.Prime] (N : Subgroup G) [N.Normal] (hN : Nat.card N = p)
    (hgen : IsEGenerated i (G ⧸ N)) : IsEGenerated i G := by
  have hpN : IsPGroup p N := IsPGroup.of_card (n := 1) (by simpa using hN)
  intro T Ω hΩ
  let M := eFamilySubgroup i (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hMN : M ⊔ N = ⊤ := generation_modulo_normal T hΩ N hgen
  suffices hNM : N ≤ M by
    change M = ⊤
    simpa only [sup_eq_left.mpr hNM] using hMN
  by_cases hp2 : p = 2
  · have hNtwo : IsPGroup 2 N := hp2 ▸ hpN
    exact ((hNtwo.le_sylow_of_normal T).trans
      (sylow_le_weakClosure_normalizer T hΩ)).trans le_sup_right
  have hcomm (A : Subgroup G) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G)) :
      ⁅N,A⁆ ≤ M := by
    let _ := hΩ.1 A hA
    have hAE : eSubgroup i (T : Subgroup G) A ≤ eFamilySubgroup i (T : Subgroup G) Ω :=
      le_iSup_of_le (⟨A, hA, hAT⟩ : {A : Subgroup G // A ∈ Ω ∧ A ≤ (T : Subgroup G)}) le_rfl
    exact (odd_normal_commutator_le_eSubgroup_one hp2 T N A hpN hAT).trans
      ((eSubgroup_mono _ _ hi).trans (hAE.trans le_sup_left))
  have : Fact (Nat.card N).Prime := ⟨by simpa only [hN] using (Fact.out : p.Prime)⟩
  rcases ((N ⊓ M).subgroupOf N).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hinf : N ⊓ M = ⊥ := by
      have hm := congrArg (Subgroup.map N.subtype) hb
      simpa only [map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_bot] using hm
    have hNW : N ≤ centralizer (weakClosure (T : Subgroup G) Ω : Set G) := by
      apply le_centralizer_iff.mpr
      apply sSup_le
      intro A hA
      apply le_centralizer_iff.mp
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply le_bot_iff.mp
      rw [← hinf]
      exact le_inf (commutator_le_left N A) (hcomm A hA.1 hA.2)
    exact (hNW.trans (centralizer_le_normalizer _)).trans le_sup_right
  · have hinf : N ⊓ M = N := by
      have hm := congrArg (Subgroup.map N.subtype) ht
      simpa only [map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,
        range_subtype] using hm
    exact hinf.symm.le.trans inf_le_right

end CFSG.Quasithin.ChapterE
