module
public import Theory.GroupTheory.TwoOrbitThree.PairedAction
public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# Three-prime centralizers of commuting factors detected in a two-local

A four-group in the first factor with symmetric-four normalizer supplies
one three-rank inside its genuine two-local normalizer. A commuting,
centerless factor divisible by three supplies the other. Quasithinness
therefore forces the centralizer of the full pair to have three-prime order.
This avoids imposing any local rank bound on a component normalizer.

Source: Aschbacher--Smith, the first residual calculation in 2.5.20, p.564.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G:Type*} [Group G] [Finite G]
/-- Restriction to a specified local factor suffices for the pair centralizer. -/
theorem pair_centralizer_coprime_three_of_local_factor
    (K L J N:Subgroup G) (hJK:J≤K) (hJN:J≤N) (hLN:L≤N)
    (hCN:centralizer ((K⊔L:Subgroup G):Set G)≤N)
    (hcomm:K≤centralizer (L:Set G))
    (hzJ:center J=⊥) (hzL:center L=⊥)
    (hdJ:3∣Nat.card J) (hdL:3∣Nat.card L) (hr:primeRank 3 N≤2) :
    Nat.Coprime 3 (Nat.card (centralizer ((K⊔L:Subgroup G):Set G))) := by
  let A:=J.subgroupOf N
  let B:=L.subgroupOf N
  let C:=centralizer ((K⊔L:Subgroup G):Set G)
  let eA:A≃*J:=subgroupOfEquivOfLe hJN
  let eB:B≃*L:=subgroupOfEquivOfLe hLN
  have hzA:center A=⊥:=by
    apply bot_unique
    intro x hx
    have hh:eA x∈center J:=(centerCongr eA ⟨x,hx⟩).property
    rw [hzJ] at hh
    exact eA.injective ((mem_bot.mp hh).trans (map_one eA).symm)
  have hzB:center B=⊥:=by
    apply bot_unique
    intro x hx
    have hh:eB x∈center L:=(centerCongr eB ⟨x,hx⟩).property
    rw [hzL] at hh
    exact eB.injective ((mem_bot.mp hh).trans (map_one eB).symm)
  have hAB:⁅A,B⁆=⊥:=by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha b hb
    exact Subtype.ext (hcomm (hJK ha) b hb)
  have hc:=TwoOrbitThree.centralizer_join_coprime_three A B hAB
    hzA hzB
    (by simpa only [Nat.card_congr eA.toEquiv] using hdJ)
    (by simpa only [Nat.card_congr eB.toEquiv] using hdL) hr
  have hC:C.subgroupOf N≤centralizer ((A⊔B:Subgroup N):Set N):=by
    apply le_centralizer_iff.mp
    apply sup_le
    · intro a ha c hc
      exact Subtype.ext ((hc a (mem_sup_left (hJK ha))).symm)
    · intro a ha c hc
      exact Subtype.ext ((hc a (mem_sup_right ha)).symm)
  have hd:=card_dvd_of_le hC
  rw [Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at hd
  exact hc.of_dvd_right hd
private theorem symmetric_four_center : center (Equiv.Perm (Fin 4)) = ⊥ := by
  have h : ∀ a : Equiv.Perm (Fin 4), (∀ b, a * b = b * a) → a = 1 := by
    decide +kernel
  apply bot_unique
  intro a ha
  exact h a (fun b => (mem_center_iff.mp ha b).symm)

/-- The actual normalizer of a four-group supplies the needed two-local rank bound. -/
theorem pair_centralizer_coprime_three_of_four_normalizer
    (hG : IsQuasithin G) (K L : Subgroup G) (F : Subgroup K) [IsKleinFour F]
    (eF : normalizer (F : Set K) ≃* Equiv.Perm (Fin 4))
    (hcomm : K ≤ centralizer (L : Set G))
    (hzL : center L = ⊥) (hdL : 3 ∣ Nat.card L) :
    Nat.Coprime 3 (Nat.card (centralizer ((K ⊔ L : Subgroup G) : Set G))) := by
  let E := F.map K.subtype
  let J := (normalizer (F : Set K)).map K.subtype
  let N := normalizer (E : Set G)
  let eJ : J ≃* Equiv.Perm (Fin 4) :=
    ((normalizer (F : Set K)).equivMapOfInjective K.subtype K.subtype_injective).symm.trans eF
  have hJK : J ≤ K := map_subtype_le _
  have hJN : J ≤ N := le_normalizer_map K.subtype
  have hEK : E ≤ K := map_subtype_le _
  have hLN : L ≤ N := (le_centralizer_iff.mp hcomm).trans
    ((centralizer_le hEK).trans (centralizer_le_normalizer _))
  have hCN : centralizer ((K ⊔ L : Subgroup G) : Set G) ≤ N :=
    (centralizer_le (hEK.trans le_sup_left)).trans (centralizer_le_normalizer _)
  have hJE : center J = ⊥ := by
    apply bot_unique
    intro x hx
    have he : eJ x ∈ center (Equiv.Perm (Fin 4)) := (centerCongr eJ ⟨x, hx⟩).property
    rw [symmetric_four_center, mem_bot] at he
    exact eJ.map_eq_one_iff.mp he
  have hdJ : 3 ∣ Nat.card J := by
    rw [Nat.card_congr eJ.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hcE : Nat.card E = 4 := by
    rw [card_map_of_injective K.subtype_injective]
    exact IsKleinFour.card_four
  have hE : E ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcE
    omega
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hpE : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 F).map K.subtype
  have hr : primeRank 3 N ≤ 2 :=
    isQuasithin_iff_twoLocal.mp hG N ⟨E, hE, hpE, rfl⟩ 3 Nat.prime_three (by decide)
  exact pair_centralizer_coprime_three_of_local_factor K L J N
    hJK hJN hLN hCN hcomm hJE hzL hdJ hdL hr
end Theory.GroupTheory
