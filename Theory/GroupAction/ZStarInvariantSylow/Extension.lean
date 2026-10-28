module

public import Theory.GroupAction.OddInvariantSylow
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.Involution.Basic
public import Theory.PPrimeCore

/-!
# Invariant Sylow extension for actions trivial modulo an odd normal subgroup

Suppose a two-group acts on a finite group and every displacement lies in an
odd normal subgroup N. Any invariant p-subgroup, for p odd, extends to an
invariant Sylow p-subgroup. Choose an ordinary Sylow B containing the given
subgroup. The group N B is odd, is invariant because it contains every
displacement, and contains a Sylow subgroup of the whole group. The odd-order
invariant Sylow extension theorem therefore gives the required witness.

The final theorem treats an external involution normalizing W, with
[W, <t>] contained in the image of O₂′(W). It uses the literal conjugation
action on W and returns the Sylow subgroup through W's subtype map.

Source: GLS4, Chapter 2, Proposition 3.7(a), printed p.30, citing [Hi; 4.1].
-/

namespace ZStarInvariantSylow

open Subgroup
open BenderSuzuki.PFAppendixIII
open scoped commutatorElement

private theorem odd_card_sup_of_normal
    {G : Type*} [Group G] [Finite G] (N B : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (hB : Odd (Nat.card B)) :
    Odd (Nat.card (N ⊔ B : Subgroup G)) := by
  let H : Subgroup G := N ⊔ B
  have hi : (N.subgroupOf H).index ∣ Nat.card B := by
    change N.relIndex (N ⊔ B) ∣ Nat.card B
    rw [relIndex_sup_left]
    exact relIndex_dvd_card N B
  have hc : Odd (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show N ≤ H from le_sup_left)).toEquiv]
    exact hN
  rw [← (N.subgroupOf H).card_mul_index]
  exact hc.mul (hB.of_dvd_nat hi)

private theorem invariant_of_displacements_mem
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (N H : Subgroup G) (hNH : N ≤ H)
    (hdisp : ∀ (a : A) (x : G), (a • x) * x⁻¹ ∈ N) :
    IsInvariant A G H := by
  have hf (a : A) (x : G) (hx : x ∈ H) : a • x ∈ H := by
    simpa only [inv_mul_cancel_right] using H.mul_mem (hNH (hdisp a x)) hx
  exact ⟨fun a x => ⟨hf a x, fun hx => by
    simpa only [inv_smul_smul] using hf a⁻¹ (a • x) hx⟩⟩

/-- A two-group action trivial modulo an odd normal subgroup admits invariant
Sylow extensions for every invariant subgroup of odd prime-power order. -/
public theorem exists_invariant_sylow_of_odd_normal_displacement
    {G A : Type*} [Group G] [Finite G] [Group A]
    [MulDistribMulAction A G] (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (hdisp : ∀ (a : A) (x : G), (a • x) * x⁻¹ ∈ N)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup G) (hP : IsPGroup p P) (hPI : IsInvariant A G P) :
    ∃ Q : Sylow p G, P ≤ (Q : Subgroup G) ∧
      IsInvariant A G (Q : Subgroup G) := by
  classical
  obtain ⟨B, hPB⟩ := hP.exists_le_sylow
  let H : Subgroup G := N ⊔ (B : Subgroup G)
  have hBH : (B : Subgroup G) ≤ H := le_sup_right
  have hPH : P ≤ H := hPB.trans hBH
  have hBodd : Odd (Nat.card (B : Subgroup G)) := by
    rw [B.card_eq_multiplicity]
    exact hpodd.pow
  have hHodd : Odd (Nat.card H) := odd_card_sup_of_normal N B hNodd hBodd
  let : IsInvariant A G H := invariant_of_displacements_mem N H le_sup_left hdisp
  let : IsInvariant A G P := hPI
  have hPHp : IsPGroup p (P.subgroupOf H) :=
    hP.of_equiv (subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hPQ, hQI⟩ := exists_invariant_sylow_le_of_isPGroup hA hHodd
    (P.subgroupOf H) hPHp (isInvariant_subgroupOf P H)
  let : IsInvariant A H (Q : Subgroup H) := hQI
  let QG : Subgroup G := (Q : Subgroup H).map H.subtype
  have hQGI : IsInvariant A G QG := isInvariant_map_subtype H (Q : Subgroup H)
  have hPQG : P ≤ QG := by
    intro x hx
    exact ⟨⟨x, hPH hx⟩, hPQ hx, rfl⟩
  have hc : Nat.card QG = p ^ (Nat.card G).factorization p := by
    calc
      Nat.card QG = Nat.card (Q : Subgroup H) := card_map_of_injective H.subtype_injective
      _ = p ^ (Nat.card H).factorization p := Q.card_eq_multiplicity
      _ = Nat.card ((B.subtype hBH : Sylow p H) : Subgroup H) :=
        (B.subtype hBH).card_eq_multiplicity.symm
      _ = Nat.card (B : Subgroup G) :=
        Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
      _ = p ^ (Nat.card G).factorization p := B.card_eq_multiplicity
  exact ⟨Sylow.ofCard QG hc, hPQG, hQGI⟩

/-- Ambient commutator containment gives the displacement condition for the
literal conjugation action on the normalized subgroup. -/
public theorem displacement_mem_of_commutator_le
    {G : Type*} [Group G] {A W : Subgroup G} [Normalizes A W]
    {N : Subgroup W} (hcore : ⁅W, A⁆ ≤ N.map W.subtype)
    (a : A) (x : W) : (a • x) * x⁻¹ ∈ N := by
  have hc : ⁅(a : G), (x : G)⁆ ∈ N.map W.subtype := by
    apply hcore
    rw [commutator_comm]
    exact commutator_mem_commutator a.property x.property
  obtain ⟨y, hy, he⟩ := hc
  have he' : y = (a • x) * x⁻¹ := by
    apply Subtype.ext
    exact he
  exact he' ▸ hy

/-- An external involution acting trivially modulo the odd core of W admits
an invariant Sylow extension inside W. No oddness assumption on W is needed. -/
public theorem exists_invariant_sylow_containing
    {G : Type*} [Group G] [Finite G] {t : G} (ht : IsInvolution t)
    {W : Subgroup G} (htW : t ∈ normalizer (W : Set G))
    (hcore : ⁅W, zpowers t⁆ ≤ (pPrimeCore 2 W).map W.subtype)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {P : Subgroup G} (hP : IsPGroup p P) (hPW : P ≤ W)
    (htP : t ∈ normalizer (P : Set G)) :
    ∃ Q : Sylow p W, P ≤ (Q : Subgroup W).map W.subtype ∧
      t ∈ normalizer (((Q : Subgroup W).map W.subtype) : Set G) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let A : Subgroup G := zpowers t
  have hAW : A ≤ normalizer (W : Set G) := zpowers_le.mpr htW
  have hAP : A ≤ normalizer (P : Set G) := zpowers_le.mpr htP
  let : Normalizes A W := ⟨hAW⟩
  have hA : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card (zpowers t) = 2 ^ 1
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
  have hdisp (a : A) (x : W) : (a • x) * x⁻¹ ∈ pPrimeCore 2 W := by
    exact displacement_mem_of_commutator_le hcore a x
  have hPI : IsInvariant A W (P.subgroupOf W) := by
    refine ⟨fun a x => ?_⟩
    change (x : G) ∈ P ↔ (a : G) * (x : G) * (a : G)⁻¹ ∈ P
    exact mem_normalizer_iff.mp (hAP a.property) (x : G)
  obtain ⟨Q, hPQ, hQI⟩ := exists_invariant_sylow_of_odd_normal_displacement
    hA (pPrimeCore 2 W) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    hdisp hpodd (P.subgroupOf W)
    (hP.of_equiv (subgroupOfEquivOfLe hPW).symm) hPI
  refine ⟨Q, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPW hx⟩, hPQ hx, rfl⟩
  · rw [mem_normalizer_iff]
    intro x
    have hf (a : A) (x : G) (hx : x ∈ (Q : Subgroup W).map W.subtype) :
        (a : G) * x * (a : G)⁻¹ ∈ (Q : Subgroup W).map W.subtype := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a • y, (hQI.invariant a y).mp hy, rfl⟩
    let a : A := ⟨t, mem_zpowers t⟩
    constructor
    · exact hf a x
    · intro hx
      simpa [a, mul_assoc] using hf a⁻¹ (t * x * t⁻¹) hx

end ZStarInvariantSylow
