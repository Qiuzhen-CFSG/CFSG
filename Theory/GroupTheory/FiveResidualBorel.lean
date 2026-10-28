module
public import Theory.GroupTheory.GeneralizedFitting.Solvable
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CoprimeIndexMarking
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# Detecting an order-five residual from a failed characteristic-two extension

Let a finite solvable group be YB, with Y normal and two-perfect,
|Y:O₂(Y)|=5, and B a characteristic-two subgroup of index five whose
order is prime to five. If the group itself fails characteristic two,
its nontrivial odd core is disjoint from B, hence has order five. This
core lies in Y, and the two-perfect condition forces it to be all of Y.

The image theorem retains a surjection with two-group kernel contained in
B. Such a map preserves the core quotient and the Borel index. The companion
index calculation constructs that index from O₂(Y)≤B and the prime-to-five
order condition. Both are consumed by the literal quotient in original15.2.4.
Source: Aschbacher--Smith, original15.2.4, printed p.1106.
-/

open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem normal_disjoint_card_dvd_index (N B : Subgroup G) [N.Normal]
    (hNB : N ⊓ B = ⊥) : Nat.card N ∣ B.index := by
  have hi := relIndex_mul_index (show N ≤ N ⊔ B from le_sup_left)
  rw [relIndex_sup_left,←inf_relIndex_right,hNB,relIndex_bot_left] at hi
  refine ⟨(N ⊔ B).index,?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B))
  calc
    Nat.card B * B.index = Nat.card G := B.card_mul_index
    _ = Nat.card N * N.index := N.card_mul_index.symm
    _ = Nat.card B * (Nat.card N * (N ⊔ B).index) := by rw [←hi]; ring

private theorem five_residual_card_of_failed_borel
    [Group.IsSolvable G] (Y B : Subgroup G) [Y.Normal]
    (hY : IsPPerfect 2 Y) (hc : (pCore 2 Y).index = 5)
    (hgen : Y ⊔ B = ⊤) (hB5 : ¬ 5 ∣ Nat.card B) (hi : B.index = 5)
    (hB : generalizedFitting B = pCore 2 B)
    (hfail : generalizedFitting G ≠ pCore 2 G) : Nat.card Y = 5 := by
  let N := pPrimeCore 2 G
  have hn : N ≠ ⊥ := by
    intro hb
    apply hfail
    rw [generalizedFitting_eq_fitting_of_solvable,Fitting_eq_pcore G 2 hb]
  have hBo : pPrimeCore 2 B = ⊥ := by
    apply pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    rw [←hB]
    exact centralizer_generalizedFitting_le _
  have hNB : N ⊓ B = ⊥ := normal_coprime_inf_eq_bot N B pPrimeCore_coprime_card hBo
  have hd : Nat.card N ∣ 5 := hi ▸ normal_disjoint_card_dvd_index N B hNB
  have hcardN : Nat.card N = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h1 | h5
    · exact (hn ((Subgroup.card_eq_one).mp h1)).elim
    · exact h5
  have hiY : Y.index = Y.relIndex B := by
    rw [←relIndex_top_right,←hgen,relIndex_sup_left]
  have hY5 : ¬ 5 ∣ Y.index := fun hh => hB5 (hh.trans (hiY ▸ relIndex_dvd_card Y B))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hN5 : IsPGroup 5 N := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hcardN)
  have hNY : N ≤ Y := hN5.le_normal_of_index_primeTo Y N hY5
  let R := N.subgroupOf Y
  let : R.Normal := inferInstance
  have hcardR : Nat.card R = 5 := (Nat.card_congr (subgroupOfEquivOfLe hNY).toEquiv).trans hcardN
  obtain ⟨n,hnc⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hcardY : Nat.card Y = 5 * 2 ^ n := by
    have hh := (pCore 2 Y).card_mul_index
    rw [hc,hnc] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  have hquot : IsPGroup 2 (Y ⧸ R) := by
    apply IsPGroup.of_card (n := n)
    have hh := R.card_mul_index
    rw [hcardR,hcardY] at hh
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) hh
  have hR : R = ⊤ := hY R inferInstance hquot
  have hYN : Y ≤ N := subgroupOf_eq_top.mp hR
  exact (congrArg (fun U : Subgroup G => Nat.card U) (le_antisymm hYN hNY)).trans hcardN

/-- The core index and absence of five in B give [YB:B]=5. -/
public theorem index_five_of_core_le_borel (Y B : Subgroup G)
    (hc : (pCore 2 Y).index = 5) (hcore : Y.pCoreIn 2 ≤ B)
    (hn : B ≤ normalizer (Y : Set G))
    (hB : ¬ 5 ∣ Nat.card B) : B.relIndex (Y ⊔ B) = 5 := by
  have hle : pCore 2 Y ≤ B.subgroupOf Y := fun x hx => hcore (mem_map_of_mem Y.subtype hx)
  have hd : (B.subgroupOf Y).index ∣ 5 := hc ▸ index_dvd_of_le hle
  have hn1 : (B.subgroupOf Y).index ≠ 1 := by
    intro hh
    have hYB : Y ≤ B := subgroupOf_eq_top.mp (index_eq_one.mp hh)
    exact hB ((hc ▸ (pCore 2 Y).index_dvd_card).trans (card_dvd_of_le hYB))
  have hi : (B.subgroupOf Y).index = 5 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left hn1
  rw [relIndex_sup_of_normalizes Y B hn]
  exact hi

/-- A failed characteristic-two image has residual image of order five. -/
public theorem five_image_of_failed_borel
    {D : Type*} [Group D] [Finite D] [Group.IsSolvable G]
    (f : G →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (Y B : Subgroup G) [Y.Normal]
    (hY : IsPPerfect 2 Y) (hc : (pCore 2 Y).index = 5)
    (hgen : Y ⊔ B = ⊤) (hB5 : ¬ 5 ∣ Nat.card B) (hi : B.index = 5)
    (hker : f.ker ≤ B) (hB : generalizedFitting (B.map f) = pCore 2 (B.map f))
    (hfail : generalizedFitting D ≠ pCore 2 D) : Nat.card (Y.map f) = 5 := by
  let : Group.IsSolvable D := Group.isSolvable_of_surjective hf
  let : (Y.map f).Normal := Normal.map inferInstance f hf
  have hperf := hY.of_surjective (f.subgroupMap Y) (f.subgroupMap_surjective Y)
  have hkY : IsPGroup 2 (f.subgroupMap Y).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have he := MonoidHom.pCoreQuotientEquiv (f.subgroupMap Y) (f.subgroupMap_surjective Y) hkY
  have hci : (pCore 2 (Y.map f)).index = 5 := (Nat.card_congr he.toEquiv).symm.trans hc
  have hgi : Y.map f ⊔ B.map f = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ hf]
  have hBi : ¬ 5 ∣ Nat.card (B.map f) := fun hh => hB5 (hh.trans (card_map_dvd _ _))
  have hii : (B.map f).index = 5 := by rw [index_map_eq B hf hker,hi]
  exact five_residual_card_of_failed_borel (Y.map f) (B.map f) hperf hci hgi hBi hii hB hfail


end Subgroup
