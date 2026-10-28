module

public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.SelfCentralizingNormalFourRecognition
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Splitting a central involution at a core-free half-Sylow subgroup

A central subgroup of order two meets a core-free subgroup trivially.
When their orders fill an index-three overgroup, Gaschütz extends this
local complement to the whole group. In an order-forty-eight group with
a self-centralizing normal subgroup of order eight, the complement has
a self-centralizing normal four and is therefore S₄.

This is the group recognition step in Aschbacher–Smith F.6.5(2)(v), p.305.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

 theorem central_two_complement_of_corefree_half
    (Z H R : Subgroup G) (hZ : Z ≤ center G) (hZH : Z ≤ H)
    (hZcard : Nat.card Z = 2) (hHcard : Nat.card H = 16)
    (hRcard : Nat.card R = 8) (hGcard : Nat.card G = 48)
    (hRH : R ≤ H) (hcore : R.normalCore = ⊥) :
    ∃ K : Subgroup G, Z.IsComplement' K := by
  let : Z.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hZ hx) g, mul_inv_cancel_right]
    exact hx⟩
  let : IsCyclic Z := isCyclic_of_prime_card hZcard
  have hdis : Disjoint Z R := by
    let : Fact (Nat.card Z).Prime := ⟨hZcard ▸ Nat.prime_two⟩
    rcases (R.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with hh | hh
    · apply disjoint_def.mpr
      intro x hxZ hxR
      have hx : (⟨x,hxZ⟩ : Z) ∈ R.subgroupOf Z := hxR
      rw [hh] at hx
      exact congrArg Subtype.val (mem_bot.mp hx)
    · have hZR : Z ≤ R := fun z hz =>
        (show (⟨z,hz⟩ : Z) ∈ R.subgroupOf Z from hh ▸ mem_top _)
      have hb : Z = ⊥ := le_bot_iff.mp (hcore ▸ normal_le_normalCore.mpr hZR)
      rw [hb, card_bot] at hZcard
      omega
  have hi : H.index = 3 := by
    have hc := H.index_mul_card
    rw [hHcard,hGcard] at hc
    omega
  apply exists_complement_of_coprime_overgroup Z H hZH (by rw [hZcard,hi]; decide)
  refine ⟨R.subgroupOf H, isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv, hZcard,hRcard,hHcard]
  · apply disjoint_def.mpr
    intro x hxZ hxR
    exact Subtype.ext (disjoint_def.mp hdis hxZ hxR)

 theorem c2_symmetric_four_of_central_complement
    (Q Z K : Subgroup G) [Q.Normal]
    (hQcard : Nat.card Q = 8)
    (hcent : centralizer (Q : Set G) ≤ Q)
    (hZ : Z ≤ center G) (hZQ : Z ≤ Q)
    (hZcard : Nat.card Z = 2) (hGcard : Nat.card G = 48)
    (hcomp : Z.IsComplement' K) :
    Nonempty (G ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  let U := Q.subgroupOf K
  have hKcard : Nat.card K = 24 := by
    have hc := hcomp.card_mul_card
    rw [hZcard,hGcard] at hc
    omega
  let m : Z × U → Q := fun x => ⟨x.1 * x.2,
    Q.mul_mem (hZQ x.1.property) x.2.property⟩
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      have he : (x.1, (x.2 : K)) = (y.1, (y.2 : K)) :=
        hcomp.1 (congrArg Subtype.val hxy)
      exact Prod.ext (congrArg (fun t : Z × K => t.1) he)
        (Subtype.ext (congrArg (fun t : Z × K => t.2) he))
    · intro q
      obtain ⟨⟨z,k⟩,he⟩ := hcomp.2 (q : G)
      have hkQ : (k : G) ∈ Q := by
        have hk : (k : G) = (z : G)⁻¹ * q := by rw [←he,inv_mul_cancel_left]
        rw [hk]
        exact Q.mul_mem (Q.inv_mem (hZQ z.property)) q.property
      exact ⟨(z,⟨k,hkQ⟩),Subtype.ext he⟩
  have hUcard : Nat.card U = 4 := by
    have hc := Nat.card_congr (Equiv.ofBijective m hm)
    rw [Nat.card_prod,hZcard,hQcard] at hc
    omega
  have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by simpa using hUcard)
  have hUc : centralizer (U : Set K) ≤ U := by
    intro x hx
    apply hcent
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨⟨z,k⟩,he⟩ := hcomp.2 q
    have hkQ : (k : G) ∈ Q := by
      have hk : (k : G) = (z : G)⁻¹ * q := by rw [←he,inv_mul_cancel_left]
      rw [hk]
      exact Q.mul_mem (Q.inv_mem (hZQ z.property)) hq
    have hkx : (k : G) * x = (x : G) * k :=
      congrArg Subtype.val (mem_centralizer_iff.mp hx k hkQ)
    have hzx : (z : G) * x = (x : G) * z :=
      (mem_center_iff.mp (hZ z.property) x).symm
    change (z : G) * (k : G) = q at he
    change q * (x : G) = (x : G) * q
    rw [←he,mul_assoc,hkx,←mul_assoc,hzx,mul_assoc]
  obtain ⟨eK⟩ := mulEquiv_perm_four_of_selfCentralizing_normal_four U hUp hUcard hUc hKcard
  let mult : Z × K →* G := Z.subtype.noncommCoprod K.subtype
    (fun z k => (mem_center_iff.mp (hZ z.property) k).symm)
  let eG : G ≃* Z × K := (MulEquiv.ofBijective mult hcomp).symm
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hZcard (by
    simp [Nat.card_eq_fintype_card])
  exact ⟨eG.trans (MulEquiv.prodCongr eZ eK)⟩
end Theory.GroupTheory
