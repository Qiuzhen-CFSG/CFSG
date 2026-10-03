module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum

/-!
# Centralizers from inverted square roots

Let a finite group D embed in G. Suppose an actor inverts an order-four
rotation of D and an element commuting with D, and those two elements have
the same square. Their product is fixed and has square one. If the actor's full
centralizer is elementary abelian, every fixed element of D commutes with
that product, hence with the rotation. When the rotation has cyclic
centralizer in D, the fixed subgroup of D is cyclic of exponent two.
The rotation's square is a nonidentity fixed element, so this subgroup
has exactly two elements.

This separates the counting argument from the construction of square roots
in the quaternion and Hall factors of Janko–Thompson, Math. Z. 113 (1970),
§4, p.392, Case 1. The explicit embedding retains the concrete ambient
intersection needed by that application.
-/

open Subgroup

/-- Two inverted commuting square roots with common square force a cyclic
tail's fixed subgroup to have order two. Only the centralizer of the chosen
rotation in the tail is assumed cyclic. -/
public theorem Subgroup.card_inf_centralizer_eq_two_of_inverted_square_roots
    {D G : Type*} [Group D] [Finite D] [Group G]
    (f : D →* G) (hf : Function.Injective f) (v a : G) (r : D)
    (hr : orderOf r = 4) (hc : ∀ d : D, Commute a (f d))
    (hs : a ^ 2 = f (r ^ 2))
    (ha : v * a * v⁻¹ = a⁻¹) (hv : v * f r * v⁻¹ = (f r)⁻¹)
    [IsCyclic (centralizer ({r} : Set D))]
    [IsElementaryAbelian 2 (centralizer ({v} : Set G))] :
    Nat.card (f.range ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 := by
  let C := centralizer ({v} : Set G)
  let K := C.comap f
  have hq2 : (a * f r) ^ 2 = 1 := by
    rw [(hc r).mul_pow, hs, ← map_pow, ← map_mul, ← pow_add]
    change f (r ^ 4) = 1
    rw [← hr, pow_orderOf_eq_one, map_one]
  have hqC : a * f r ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    symm
    apply (mul_inv_eq_iff_eq_mul).mp
    change MulAut.conj v (a * f r) = a * f r
    rw [map_mul]
    change (v * a * v⁻¹) * (v * f r * v⁻¹) = a * f r
    rw [ha, hv, (hc r).inv_inv.eq, ← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hq2)
  have hKC : K ≤ centralizer ({r} : Set D) := by
    intro d hd
    have hdf : f d ∈ C := hd
    have hcomm : Commute (a * f r) (f d) := C.le_centralizer hdf _ hqC
    apply mem_centralizer_singleton_iff.mpr
    apply hf
    simp only [map_mul]
    apply mul_left_cancel (a := a)
    calc
      a * (f d * f r) = f d * (a * f r) := by rw [← mul_assoc, (hc d).eq, mul_assoc]
      _ = a * f r * f d := hcomm.eq.symm
      _ = a * (f r * f d) := mul_assoc _ _ _
  let : IsCyclic K := isCyclic_of_injective (inclusion hKC) (inclusion_injective hKC)
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hk2 : k ^ 2 = 1 := by
    apply Subtype.ext
    apply hf
    change f ((k : D) ^ 2) = f 1
    simpa only [map_pow, map_one] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := C) (f k) k.property
  have hupper : Nat.card K ≤ 2 := by
    rw [← hk]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hk2)
  have hr2K : r ^ 2 ∈ K := by
    apply mem_centralizer_singleton_iff.mpr
    symm
    apply (mul_inv_eq_iff_eq_mul).mp
    change MulAut.conj v (f (r ^ 2)) = f (r ^ 2)
    rw [map_pow, map_pow]
    change (v * f r * v⁻¹) ^ 2 = (f r) ^ 2
    rw [hv, inv_pow, ← map_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, ← pow_add]
    change f (r ^ 4) = 1
    rw [← hr, pow_orderOf_eq_one, map_one]
  have hlower : 2 ≤ Nat.card K := by
    have hord : orderOf (⟨r ^ 2, hr2K⟩ : K) = 2 := by
      rw [← orderOf_coe, orderOf_pow, hr]
      decide
    exact Nat.le_of_dvd Nat.card_pos
      (hord ▸ _root_.orderOf_dvd_natCard (x := (⟨r ^ 2, hr2K⟩ : K)))
  have heq : Nat.card K = 2 := by omega
  rw [← map_comap_eq, card_map_of_injective hf]
  exact heq
