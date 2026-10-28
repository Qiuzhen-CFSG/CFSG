module
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Vanishing of transfer through an index-two subgroup

Transfer into a commutative image of an index-two subgroup kills an element
whose square and commutators lie in that subgroup's derived subgroup.
The proof computes the orbit formula for ordinary transfer. For an element
inside the subgroup, conjugated powers have the same image modulo the
derived subgroup and their exponents sum to two. For an element outside,
each orbit has even length and its contribution is trivial.

This is the elementary index-two calculation used in the proof of
Andersen–Oliver–Ventura, `Fusion systems and amalgams`, Proposition 2.3(b),
author manuscript p.6. It is stated for ordinary group transfer and needs
no fusion-system assumptions.
-/

open scoped commutatorElement

namespace MonoidHom

public theorem transfer_eq_one_of_index_two
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    (M : Subgroup G) (hM : M.index = 2) (u : G)
    (hsquare : u ^ 2 ∈ ⁅M, M⁆)
    (hcomm : ∀ v : G, ⁅u, v⁆ ∈ ⁅M, M⁆)
    (φ : M →* A) : MonoidHom.transfer φ u = 1 := by
  classical
  let : M.Normal := M.normal_of_index_eq_two hM
  let N : Subgroup G := ⁅M, M⁆
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hkill (x : M) (hx : (x : G) ∈ N) : φ x = 1 := by
    change (x : G) ∈ ⁅M, M⁆ at hx
    rw [← M.map_subtype_commutator] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have heq : y = x := Subtype.ext hxy
    subst y
    exact Abelianization.commutator_subset_ker φ hy
  have hcommute (v : G) : Commute (q u) (q v) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N) (x := ⁅u, v⁆)).mpr (hcomm v)
  have hconj (k : ℕ) (v : G) : q (v⁻¹ * u ^ k * v) = q (u ^ k) := by
    simp only [map_mul, map_inv, map_pow]
    rw [mul_assoc, (hcommute v).pow_left k |>.eq, inv_mul_cancel_left]
  have hsame (x y : M) (hxy : q x = q y) : φ x = φ y := by
    have hmem : ((x : G)⁻¹ * (y : G)) ∈ N := QuotientGroup.eq.mp hxy
    have hone := hkill (x⁻¹ * y) hmem
    simpa only [map_mul, map_inv, inv_mul_eq_one] using hone
  let := Fintype.ofFinite (G ⧸ M)
  let := Fintype.ofFinite
    (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ M)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  by_cases hu : u ∈ M
  · let uM : M := ⟨u, hu⟩
    calc
      _ = ∏ orbit : Quotient
          (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ M)),
          φ uM ^ Function.minimalPeriod (u • ·) orbit.out := by
        apply Finset.prod_congr rfl
        intro orbit _
        rw [← map_pow]
        exact hsame _ _ (hconj _ _)
      _ = φ uM ^ M.index := by
        rw [Finset.prod_pow_eq_pow_sum, Subgroup.index_eq_sum_minimalPeriod M u]
      _ = 1 := by
        rw [hM, ← map_pow]
        exact hkill (uM ^ 2) hsquare
  · apply Finset.prod_eq_one
    intro orbit _
    let k := Function.minimalPeriod (u • ·) orbit.out
    let v : G := orbit.out.out
    have hmem : v⁻¹ * u ^ k * v ∈ M :=
      QuotientGroup.out_conj_pow_minimalPeriod_mem M u orbit.out
    have hupow : u ^ k ∈ M := by
      have h := (inferInstance : M.Normal).conj_mem _ hmem v
      simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] using h
    have horder : orderOf (QuotientGroup.mk' M u) = 2 := by
      have hdiv : orderOf (QuotientGroup.mk' M u) ∣ 2 := by
        simpa only [← M.index_eq_card, hM] using
          (orderOf_dvd_natCard (QuotientGroup.mk' M u))
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
      · have hzero := orderOf_eq_one_iff.mp hone
        exact (hu ((QuotientGroup.eq_one_iff (N := M) (x := u)).mp hzero)).elim
      · exact htwo
    have hk : 2 ∣ k := by
      rw [← horder]
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := M) (x := u ^ k)).mpr hupow
    obtain ⟨j, hj⟩ := hk
    have hpow : u ^ k ∈ N := by
      rw [hj, pow_mul]
      exact N.pow_mem hsquare j
    apply hkill
    exact (inferInstance : N.Normal).conj_mem' _ hpow v

end MonoidHom
