module

public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.Quasithin

/-!
# Sylow-containing two-locals from characteristic-two centralizers

Suppose every involution centralizer has a self-centralizing two-core.
Let M be a two-local containing a Sylow two-subgroup T. Its nontrivial
normal two-core meets Z(T) in an involution z. The intersection of M with
C_G(z) contains T, so it inherits characteristic two from C_G(z). It also
contains C_M(O₂(M)), and the core-centralizer overgroup criterion concludes.
All cores are intrinsic, and normality is taken in M or T as appropriate.

This is a sufficient criterion for the even-characteristic condition of
Aschbacher–Smith, printed p.3 of `refs/quasithin.pdf`. Maximality is unnecessary.
-/

namespace Theory.GroupTheory
open Subgroup

/-- Characteristic two of involution centralizers controls every two-local
containing a full Sylow two-subgroup. -/
public theorem sylow_twoLocal_centralizer_pCore_le_of_characteristic_centralizers
    {G : Type*} [Group G] [Finite G]
    (hc : ∀ z : G, orderOf z = 2 →
      centralizer (pCore 2 (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) ≤
        pCore 2 (centralizer ({z} : Set G)))
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) :
    centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨Q, hQne, hpQ, hMQ⟩ := hM
  have hQM : Q ≤ M := hMQ ▸ Q.le_normalizer
  have hQN : (Q.subgroupOf M).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hQM).mpr
    exact hMQ.le
  have hQcore : Q.subgroupOf M ≤ pCore 2 M := le_sSup ⟨hQN, hpQ.comap_subtype⟩
  have hcore_ne : pCore 2 M ≠ ⊥ := by
    intro h
    have hbot : Q.subgroupOf M = ⊥ := bot_unique (h ▸ hQcore)
    apply hQne
    rw [← map_subgroupOf_eq_of_le hQM, hbot, Subgroup.map_bot]
  let S := T.subtype hTM
  let O := pCore 2 M
  have hOS : O ≤ (S : Subgroup M) := pCore_isPGroup.le_sylow_of_normal S
  let D := O.subgroupOf (S : Subgroup M)
  have hDne : D ≠ ⊥ := by
    intro h
    apply hcore_ne
    change O = ⊥
    rw [← map_subgroupOf_eq_of_le hOS, show O.subgroupOf (S : Subgroup M) = ⊥ from h,
      Subgroup.map_bot]
  have hmeet := center_inf_ne_bot_of_normal S.isPGroup' D hDne
  let I := center S ⊓ D
  have hIp : IsPGroup 2 I := S.isPGroup'.to_subgroup I
  have hd : 2 ∣ Nat.card I := hIp.card_eq_or_dvd.resolve_left
    (fun h => hmeet (Subgroup.card_eq_one.mp h))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hd
  let t : M := z.val.val
  have htO : t ∈ O := z.property.2
  have ht : orderOf (t : G) = 2 := by
    simpa only [t, Subgroup.orderOf_coe] using hz
  let C := centralizer ({(t : G)} : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    let y : S := ⟨⟨x, hTM hx⟩, hx⟩
    exact congrArg (fun a : S => (a.val : G))
      (mem_center_iff.mp z.property.1 y)
  let N := C.subgroupOf M
  have hNchar : centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
    let H := M.subgroupOf C
    have hTH : (T.subtype hTC : Subgroup C) ≤ H := fun x hx => hTM hx
    have hHchar := centralizer_pCore_le_of_sylow_le (T.subtype hTC) H hTH (hc t ht)
    let e : N ≃* H := {
      toFun x := ⟨⟨x.val, x.property⟩, x.val.property⟩
      invFun x := ⟨⟨x.val, x.property⟩, x.val.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hHchar
  apply centralizer_pCore_le_of_overgroup 2 N hNchar
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hx t htO)).symm

end Theory.GroupTheory
