module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Square roots of central Sylow involutions

A square root of a central involution lies in its centralizer and has
2-power order. Sylow conjugacy within that centralizer moves the root into
the specified Sylow, while fixing its square. This preserves the literal
embedding of the chosen Sylow subgroup.
-/

public section
open Subgroup
open scoped Pointwise

theorem Sylow.exists_square_root_of_central_involution {K : Type*} [Group K] [Finite K]
    (R : Sylow 2 K) (u : R) (hu : u ∈ center R)
    (hu2 : (u : K) ^ 2 = 1) (hx : ∃ x : K, x ^ 2 = u) :
    ∃ y : R, y ^ 2 = u := by
  obtain ⟨x,hx⟩ := hx
  let C := centralizer ({(u : K)} : Set K)
  have hRC : (R : Subgroup K) ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hu ⟨a,ha⟩))
  let y : C := ⟨x,mem_centralizer_singleton_iff.mpr (by rw [← hx]; group)⟩
  have hy4 : y ^ (2 ^ 2) = 1 := by
    apply Subtype.ext
    change x ^ (2*2) = 1
    rw [pow_mul,hx,hu2]

  have hp : IsPGroup 2 (zpowers y) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hy4)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq C P (R.subtype hRC)
  have hyR : (MulAut.conj k) y ∈ R.subtype hRC := by
    rw [← hk]
    change (MulAut.conj k) • y ∈ (MulAut.conj k) • (P : Set C)
    exact Set.smul_mem_smul_set (hP (mem_zpowers y))
  refine ⟨⟨((MulAut.conj k) y : C),hyR⟩,?_⟩
  apply Subtype.ext
  change ((k : K) * x * (k : K)⁻¹) ^ 2 = (u : K)
  calc
    _ = (k : K) * x ^ 2 * (k : K)⁻¹ := by rw [pow_two,pow_two]; group
    _ = (u : K) := by
      rw [hx]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)

