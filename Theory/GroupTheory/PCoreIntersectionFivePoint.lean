module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

/-!
# Restricting a two-core quotient with a five-point marking

An injective subgroup of order 12288 in a group with two-core order 2048
and quotient S₅ has quotient image of order 6, 12 or 24. Its kernel is
exactly the intersection with the ambient two-core, with respective orders
2048, 1024 and 512. The proof combines the literal quotient kernel with
Lagrange's theorem and kernel-image counting.

The original Rudvalis point centralizer in Chapter13 applies this result.
It keeps the ambient quotient separate from the natural-module parabolic
quotient; the source geometry must select the order-twelve branch.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {B H : Type*} [Group B] [Group H]

/-- The ambient core intersection and its exact possible image/kernel orders. -/
theorem fivePoint_core_restriction_sizes
    (j : B →* H) (hj : Function.Injective j)
    (e : H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 5))
    (hQ : Nat.card (pCore 2 H) = 2048) (hB : Nat.card B = 12288) :
    let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 H)).comp j)
    f.ker = (pCore 2 H).comap j ∧
    f.ker.map j = j.range ⊓ pCore 2 H ∧
    ((Nat.card f.ker = 2048 ∧ Nat.card f.range = 6) ∨
      (Nat.card f.ker = 1024 ∧ Nat.card f.range = 12) ∨
      (Nat.card f.ker = 512 ∧ Nat.card f.range = 24)) := by
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 H)).comp j)
  have hk : f.ker = (pCore 2 H).comap j := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) (j x)) = 1 ↔ j x ∈ pCore 2 H
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff (j x)
  have hmap : f.ker.map j = j.range ⊓ pCore 2 H := by
    rw [hk,map_comap_eq,inf_comm]
  have hdk : Nat.card f.ker ∣ 2048 := by
    let k : f.ker →* pCore 2 H :=
      (j.comp f.ker.subtype).codRestrict _ (fun x => by
        have hh : x.val ∈ (pCore 2 H).comap j := hk ▸ x.property
        exact hh)
    have hi : Function.Injective k := fun x y h =>
      Subtype.ext (hj (congrArg Subtype.val h))
    exact hQ ▸ card_dvd_of_injective k hi
  have hmul : Nat.card f.ker * Nat.card f.range = 12288 := by
    rw [←index_ker,f.ker.card_mul_index,hB]
  have hdr : Nat.card f.range ∣ 24 := by
    have hd1 : Nat.card f.range ∣ 12288 := by
      rw [←hmul]
      exact dvd_mul_left _ _
    have hd2 : Nat.card f.range ∣ 120 := by
      have hh := f.range.card_subgroup_dvd_card
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh ⊢
      exact hh
    exact Nat.dvd_gcd hd1 hd2
  have hcases : Nat.card f.range = 1 ∨ Nat.card f.range = 2 ∨
      Nat.card f.range = 3 ∨ Nat.card f.range = 4 ∨ Nat.card f.range = 6 ∨
      Nat.card f.range = 8 ∨ Nat.card f.range = 12 ∨ Nat.card f.range = 24 := by
    have hm := Nat.mem_divisors.mpr ⟨hdr,by decide⟩
    have hd : Nat.divisors 24 = {1,2,3,4,6,8,12,24} := by decide +kernel
    rw [hd] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hkle : Nat.card f.ker ≤ 2048 := Nat.le_of_dvd (by decide) hdk
  refine ⟨hk,hmap,?_⟩
  change ((Nat.card f.ker = 2048 ∧ Nat.card f.range = 6) ∨
    (Nat.card f.ker = 1024 ∧ Nat.card f.range = 12) ∨
    (Nat.card f.ker = 512 ∧ Nat.card f.range = 24))
  rcases hcases with hh|hh|hh|hh|hh|hh|hh|hh <;> rw [hh] at hmul
  · omega
  · omega
  · omega
  · omega
  · exact Or.inl ⟨by omega,hh⟩
  · have hbad : Nat.card f.ker = 1536 := by omega
    rw [hbad] at hdk
    norm_num at hdk
  · exact Or.inr (Or.inl ⟨by omega,hh⟩)
  · exact Or.inr (Or.inr ⟨by omega,hh⟩)
end Theory.GroupTheory
