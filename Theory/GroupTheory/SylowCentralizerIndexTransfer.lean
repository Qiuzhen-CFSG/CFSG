module

public import Mathlib.GroupTheory.Sylow

/-!
# Transferring a centralizer index between Sylow subgroups

If z centralizes a Sylow p-subgroup T, extend C_T(x) to a Sylow p-subgroup
S of C_G(x). Then |S:C_S(z)| ≤ |T:C_T(x)|. Indeed C_T(x) lies in C_S(z),
while |S| ≤ |T| by Sylow conjugacy; cancel the common subgroup order.
The construction retains the containment C_T(x) ≤ S.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, proof of 16.2.3, p.1174.
The index argument works for every prime and arbitrary elements x and z.
-/

open Subgroup

/-- Transfer a centralizer index to a Sylow subgroup of an element centralizer. -/
public theorem Sylow.exists_centralizer_sylow_with_index_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (x z : G) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ S : Sylow p (centralizer ({x} : Set G)),
      (T : Subgroup G).subgroupOf (centralizer ({x} : Set G)) ≤ S ∧
      (centralizer ({z} : Set G)).relIndex
        ((S : Subgroup (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype) ≤
        (centralizer ({x} : Set G)).relIndex (T : Subgroup G) := by
  let C := centralizer ({x} : Set G)
  let A := (T : Subgroup G) ⊓ C
  obtain ⟨S, hS⟩ := (T.isPGroup'.comap_subtype (K := C)).exists_le_sylow
  let B := (S : Subgroup C).map C.subtype
  have hAB : A ≤ B := by
    intro a ha
    exact mem_map_of_mem C.subtype (hS (show (⟨a, ha.2⟩ : C) ∈
      (T : Subgroup G).subgroupOf C from ha.1))
  have hAz : A ≤ centralizer ({z} : Set G) := inf_le_left.trans hTz
  obtain ⟨R, hBR⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  have hBT : Nat.card B ≤ Nat.card T :=
    (card_le_of_le hBR).trans_eq (Nat.card_congr (R.equiv T).toEquiv)
  have hidx : A.relIndex B ≤ A.relIndex (T : Subgroup G) := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card A) _ Nat.card_pos
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le hAB
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) A (T : Subgroup G)
      bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left] at h1 h2
    rw [h1, h2]
    exact hBT
  refine ⟨S, hS, ?_⟩
  calc
    _ ≤ A.relIndex B := relIndex_le_of_le_left hAz (show (A.subgroupOf B).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
    _ ≤ A.relIndex (T : Subgroup G) := hidx
    _ = C.relIndex (T : Subgroup G) := inf_relIndex_left _ _
