module

public import CFSG.Quasithin.ChapterE.Section06.Basic
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PCoreRestriction

/-!
# Characteristic two and odd cores in escaping centralizers

The E.6 setup puts M in characteristic two. The centralizer inheritance
and normalizer criteria from 1.1.3–4 then prove every clause of E.6.6.
For the core inequality, U is normal in C_H(z), hence lies in its two-core;
restricting O₂(C_G(z)) to C_H(z) gives the required containment.
The same local characteristic-two conclusion makes O(H) intersect M
trivially, proving E.6.9(1).

`EarlierLocalFacts` states only the earlier source inputs, in their
self-centralizing-core form. They must be discharged by the owner of
Chapter 1; none is an E.6 structural conclusion. The equivalence with
the generalized-Fitting convention is proved in Theory.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.6,
E.6.9(1), and E.6.10(1), printed pp.246–249 (PDF pp.257–260).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

/-- The centralizer assertion of 1.1.3(2), the criterion 1.1.4(3),
and the Sylow-overgroup assertion 1.1.4(6). Characteristic two is stated
using the equivalent self-centralizing two-core convention of 1.1.1. -/
structure EarlierLocalFacts (T : Sylow 2 G) : Prop where
  centralizers : ∀ A B : Subgroup G, HasCharacteristicTwo B → A ≤ B →
    IsPGroup 2 A → HasCharacteristicTwo ↥(B ⊓ centralizer (A : Set G))
  central_intersection : ∀ A : Subgroup G, IsPGroup 2 A → A ≠ ⊥ →
    ((T : Subgroup G) ⊓ centralizer (T : Set G)) ⊓ A ≠ ⊥ →
    HasCharacteristicTwo (normalizer (A : Set G))
  sylow_overgroups : ∀ B : Subgroup G, B.pCoreIn 2 ≠ ⊥ → (T : Subgroup G) ≤ B →
    HasCharacteristicTwo B

theorem HypothesisE61.localCentralizer_characteristicTwo
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    {A : Subgroup G} (hAM : A ≤ M) (hAp : IsPGroup 2 A) :
    HasCharacteristicTwo ↥(M ⊓ centralizer (A : Set G)) :=
  earlier.centralizers A M
    (h.simpleQTKE.evenCharacteristic T M h.maximalTwoLocal h.sylow_le) hAM hAp

/-- E.6.6(2); the nonidentity restriction is unnecessary for this clause. -/
theorem HypothesisE61.lemma_E_6_6_2
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    {A : Subgroup G} (hAM : A ≤ M) (hAp : IsPGroup 2 A) :
    generalizedFitting ↥(M ⊓ centralizer (A : Set G)) =
      pCore 2 ↥(M ⊓ centralizer (A : Set G)) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (h.localCentralizer_characteristicTwo earlier hAM hAp)

/-- E.6.6(1), with M_H = H ∩ M. -/
theorem HypothesisE61.lemma_E_6_6_1
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V) :
    generalizedFitting ↥(centralizer (U : Set G) ⊓ M) =
      pCore 2 ↥(centralizer (U : Set G) ⊓ M) := by
  let _ := h.elementary
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (MulEquiv.subgroupCongr (inf_comm M (centralizer (U : Set G))))).mp
      (h.localCentralizer_characteristicTwo earlier
        (hU.1.trans (h.le_sylow.trans h.sylow_le))
        ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1))

theorem HypothesisE61.centralizer_fixedPoint_characteristicTwo
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    HasCharacteristicTwo (centralizer ({z} : Set G)) := by
  let _ := h.elementary
  have hzp : orderOf z = 2 := by
    have he : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz.1
    have hd := orderOf_dvd_of_pow_eq_one he
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left
      (fun ho => hne (orderOf_eq_one_iff.mp ho))
  apply earlier.sylow_overgroups
  · exact Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer hzp)
  · intro t ht
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hz.2) t ht)

theorem HypothesisE61.centralizer_fixedPoint_core_bound
    (h : HypothesisE61 K T M V) (hUV : U ≤ V)
    {z : G} (hz : z ∈ V) :
    (centralizer ({z} : Set G)).pCoreIn 2 ⊓
      centralizer ((centralizer (U : Set G) ⊓ centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
      (centralizer (U : Set G) ⊓ centralizer ({z} : Set G)).pCoreIn 2 := by
  let _ := h.elementary
  let H := centralizer (U : Set G) ⊓ centralizer ({z} : Set G)
  have hUH : U ≤ H := by
    apply le_inf
    · exact hUV.trans (V.le_centralizer.trans (Subgroup.centralizer_le hUV))
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hz) u (hUV hu))
  have hUcore : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hUV) hUH
    (inf_le_left.trans (centralizer_le_normalizer _))
  have hc : centralizer (H.pCoreIn 2 : Set G) ≤ centralizer (U : Set G) :=
    Subgroup.centralizer_le hUcore
  exact (le_inf (le_inf (inf_le_right.trans hc)
    (inf_le_left.trans (pCoreIn_le 2 _))) inf_le_left).trans
      (inf_pCoreIn_le_of_le 2 (show H ≤ centralizer ({z} : Set G) from inf_le_right))

/-- Both the generalized-Fitting equality and core bound in E.6.6(3). -/
theorem HypothesisE61.lemma_E_6_6_3
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    generalizedFitting ↥(centralizer (U : Set G) ⊓ centralizer ({z} : Set G)) =
      pCore 2 ↥(centralizer (U : Set G) ⊓ centralizer ({z} : Set G)) ∧
    (centralizer ({z} : Set G)).pCoreIn 2 ⊓
      centralizer ((centralizer (U : Set G) ⊓ centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
      (centralizer (U : Set G) ⊓ centralizer ({z} : Set G)).pCoreIn 2 := by
  let _ := h.elementary
  refine ⟨?_, h.centralizer_fixedPoint_core_bound hU.1 hz.1⟩
  have hUC : U ≤ centralizer ({z} : Set G) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hz.1) u (hU.1 hu))
  have hc := earlier.centralizers U (centralizer ({z} : Set G))
    (h.centralizer_fixedPoint_characteristicTwo earlier hz hne) hUC
    ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1)
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (MulEquiv.subgroupCongr (inf_comm (centralizer ({z} : Set G))
      (centralizer (U : Set G))))).mp hc

/-- E.6.6(4). -/
theorem HypothesisE61.lemma_E_6_6_4
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hint : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥) :
    generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) := by
  let _ := h.elementary
  have hp := (IsElementaryAbelian.isPGroup 2 V).to_le hU.1
  have hi : ((T : Subgroup G) ⊓ centralizer (T : Set G)) ⊓ U ≠ ⊥ := by
    intro he
    apply hint
    apply le_bot_iff.mp
    rw [← he]
    exact le_inf (le_inf (inf_le_left.trans (hU.1.trans h.le_sylow))
      (inf_le_right.trans inf_le_right)) inf_le_left
  have hc := earlier.centralizers U (normalizer (U : Set G))
    (earlier.central_intersection U hp hU.2.1 hi) U.le_normalizer hp
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (MulEquiv.subgroupCongr
      (inf_eq_right.mpr (centralizer_le_normalizer (U : Set G))))).mp hc

/-- E.6.10(1), whose deduction does not need the corank-one assumption. -/
theorem HypothesisE61.lemma_E_6_10_1
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hc : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥ ∨
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G))) :
    generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) :=
  hc.elim (h.lemma_E_6_6_4 earlier hU) id

/-- E.6.9(1): the actual embedded odd core of H has trivial intersection with M. -/
theorem HypothesisE61.lemma_E_6_9_1
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V) :
    (pPrimeCore 2 (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype ⊓ M = ⊥ := by
  let _ := h.elementary
  let H := centralizer (U : Set G)
  let MH := M ⊓ H
  let f : MH →* H := inclusion inf_le_right
  let C := (pPrimeCore 2 H).comap f
  have hcop : Nat.Coprime 2 (Nat.card C) :=
    Nat.Coprime.of_dvd_right
      (card_comap_dvd_of_injective (pPrimeCore 2 H) f (inclusion_injective inf_le_right))
      pPrimeCore_coprime_card
  have hC : C ≤ pPrimeCore 2 MH := le_sSup ⟨inferInstance, hcop⟩
  have hbot : pPrimeCore 2 MH = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (h.localCentralizer_characteristicTwo earlier
      (hU.1.trans (h.le_sylow.trans h.sylow_le))
      ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1))
  apply le_bot_iff.mp
  rintro x ⟨⟨y, hy, rfl⟩, hyM⟩
  have hc : (⟨y, hyM, y.property⟩ : MH) ∈ C := hy
  have he : (⟨y, hyM, y.property⟩ : MH) = 1 := by
    exact mem_bot.mp (hbot ▸ hC hc)
  exact congrArg (fun a : MH => (a : G)) he

end CFSG.Quasithin.ChapterE.Section06
