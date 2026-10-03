module
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolution

/-!
# Involution centralizers in the faithful C5 semidirect C4 model

In a semidirect product of the cyclic groups of orders five and four,
with faithful action, every involution has a cyclic centralizer of order
four. No ambient recognition or solvability hypothesis is needed.

The centralizer projects injectively into the right factor: an element
in the kernel belongs to the left factor and is fixed by the involution,
which acts there by inversion. Its order divides both two and five, so it
is the identity. This proves cyclicity and the upper bound four. A Sylow
two-subgroup containing the involution has order four and hence is abelian;
it lies in the centralizer and gives the reverse bound.

This elementary model fact supplies the involution-centralizer calculation
used in David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 3, p.675. The proof reuses the explicit inversion identity
from `FiveFourInvolution`.
-/

open Subgroup
open scoped IsMulCommutative

/-- Every involution in the faithful C5 semidirect C4 model has cyclic centralizer of order four. -/
public theorem faithful_five_four_involution_centralizer
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (y : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hy : orderOf y = 2) :
    IsCyclic (centralizer ({y} : Set _)) ∧ Nat.card (centralizer ({y} : Set _)) = 4 := by
  let C5 := Multiplicative (ZMod 5)
  let C4 := Multiplicative (ZMod 4)
  let M := C5 ⋊[φ] C4
  let : Finite M := Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup M := centralizer ({y} : Set M)
  let π : C →* C4 := SemidirectProduct.rightHom.comp C.subtype
  have hC5 : Nat.card C5 = 5 := by change Nat.card (ZMod 5) = 5; simp
  have hC4 : Nat.card C4 = 4 := by change Nat.card (ZMod 4) = 4; simp
  have hinj : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    have hxright : (x : M).right = 1 := hx
    have hxinl : (x : M) = SemidirectProduct.inl (x : M).left := by
      ext <;> simp [hxright]
    have hconj : y * SemidirectProduct.inl (x : M).left * y⁻¹ =
        SemidirectProduct.inl (x : M).left := by
      rw [← hxinl]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property).symm
    have hinv : (x : M).left⁻¹ = (x : M).left :=
      SemidirectProduct.inl_injective
        ((faithful_five_four_involution_inverts_left φ hφ y hy (x : M).left).symm.trans hconj)
    have hleft2 : (x : M).left ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← hinv]
      exact inv_mul_cancel (x : M).left
    have hleft5 : (x : M).left ^ 5 = 1 := by
      simpa only [hC5] using pow_card_eq_one' (x := (x : M).left)
    have hleft : (x : M).left = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 5)
        (orderOf_dvd_of_pow_eq_one hleft2) (orderOf_dvd_of_pow_eq_one hleft5))
    apply Subtype.ext
    rw [hxinl, hleft, map_one]
    rfl
  have hcyclic : IsCyclic C := isCyclic_of_injective π hinj
  have hupper : Nat.card C ≤ 4 :=
    (Nat.card_le_card_of_injective π hinj).trans_eq hC4
  have hY : IsPGroup 2 (zpowers y) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨S, hYS⟩ := hY.exists_le_sylow
  have hM : Nat.card M = 20 := by
    rw [SemidirectProduct.card, hC5, hC4]
  have hS : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity, hM]
    decide +kernel
  let : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hS)
  have hyS : y ∈ (S : Subgroup M) := hYS (mem_zpowers y)
  have hSC : (S : Subgroup M) ≤ C := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : S) (⟨y, hyS⟩ : S))
  have hlower : 4 ≤ Nat.card C := by
    simpa only [hS] using card_le_of_le hSC
  exact ⟨hcyclic, le_antisymm hupper hlower⟩
