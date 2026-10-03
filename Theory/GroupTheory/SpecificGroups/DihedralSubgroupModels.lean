module
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral

/-!
# Subgroups of dihedral two-groups

Every subgroup of `DihedralGroup (2 ^ n)` is cyclic or isomorphic to
`DihedralGroup (2 ^ k)` for some natural `k`. No positive lower bound on
`n` or `k` is required.

Intersect the subgroup with the cyclic rotation group. If this contains the
whole subgroup, cyclicity follows by restriction. Otherwise choose a reflection.
The rotation/reflection multiplication formulas show that this reflection and
the rotation intersection generate the subgroup, and that the reflection inverts
the intersection. The cyclic-inversion presentation then gives a dihedral model.
Lagrange's theorem makes the intersection order a divisor of `2 ^ n`, hence
another power of two.

This is the elementary dihedral subgroup argument used in Alperin–Brauer–
Gorenstein, Chapter II, Section 1, Lemma 3(i). The proof uses Mathlib's dihedral
normal forms and the reusable cyclic-inversion equivalence.
-/

namespace DihedralGroup

private theorem rotation_mem {n : ℕ} [NeZero n] (i : ZMod n) :
    r i ∈ Subgroup.zpowers (r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (r 1 : DihedralGroup n) ^ i.val = r i
  rw [r_one_pow, ZMod.natCast_zmod_val]

private theorem reflection_not_mem {n : ℕ} (i : ZMod n) :
    sr i ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
  rintro ⟨k, hk⟩
  change (r 1 : DihedralGroup n) ^ k = sr i at hk
  rw [r_one_zpow] at hk
  cases hk

public theorem subgroup_cyclic_or_dihedral_two_power {n : ℕ}
    (D : Subgroup (DihedralGroup (2 ^ n))) :
    IsCyclic D ∨ ∃ k : ℕ, Nonempty (D ≃* DihedralGroup (2 ^ k)) := by
  classical
  let R : Subgroup (DihedralGroup (2 ^ n)) := Subgroup.zpowers (r 1)
  by_cases hDR : D ≤ R
  · exact Or.inl (Subgroup.isCyclic_of_le hDR)
  right
  have hex : ∃ i : ZMod (2 ^ n), sr i ∈ D := by
    obtain ⟨x, hxD, hxR⟩ := SetLike.not_le_iff_exists.mp hDR
    cases x with
    | r i => exact False.elim (hxR (rotation_mem i))
    | sr i => exact ⟨i, hxD⟩
  obtain ⟨i, hi⟩ := hex
  let A := D ⊓ R
  have hAcyc : IsCyclic A := Subgroup.isCyclic_of_le (show A ≤ R from inf_le_right)
  have hsup : A ⊔ Subgroup.zpowers (sr i) = D := by
    apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hi)
    · intro x hx
      cases x with
      | r j => exact (le_sup_left : A ≤ A ⊔ Subgroup.zpowers (sr i)) ⟨hx, rotation_mem j⟩
      | sr j =>
        have hrot : r (j - i) ∈ A := by
          exact ⟨by simpa using D.mul_mem hi hx, rotation_mem (j - i)⟩
        have hm := (A ⊔ Subgroup.zpowers (sr i)).mul_mem
          ((le_sup_right : Subgroup.zpowers (sr i) ≤ A ⊔ Subgroup.zpowers (sr i))
            (Subgroup.mem_zpowers (sr i)))
          ((le_sup_left : A ≤ A ⊔ Subgroup.zpowers (sr i)) hrot)
        simpa using hm
  have hinv : ∀ x : DihedralGroup (2 ^ n), x ∈ A → sr i * x * (sr i)⁻¹ = x⁻¹ := by
    intro x hx
    cases x with
    | r j => simp
    | sr j => exact False.elim (reflection_not_mem j hx.2)
  obtain ⟨e⟩ := Subgroup.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    A (sr i) hAcyc (by simp [pow_two]) (fun h => reflection_not_mem i h.2) hinv
  have hdiv : Nat.card A ∣ 2 ^ n := by
    have h := Subgroup.card_dvd_of_le (show A ≤ R from inf_le_right)
    change Nat.card A ∣ Nat.card (Subgroup.zpowers (r 1 : DihedralGroup (2 ^ n))) at h
    rw [Nat.card_zpowers, orderOf_r_one] at h
    exact h
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  refine ⟨k, ?_⟩
  rw [← hk]
  exact ⟨(MulEquiv.subgroupCongr hsup.symm).trans e⟩

end DihedralGroup
