module
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section1.WreathedRelations
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The central quotient of a wreathed group

For the chosen wreathed presentation of height `n ≥ 2`, the quotient by
the center is dihedral with rotation parameter `2^n`. This proves the quotient
assertion of ABG Chapter II §1 Lemma 2(vii), article p.10.

The images of `s` and `z` generate: the central relation `u = s*t` identifies
the image of `t` with the inverse of the image of `s`. Conjugation by the
involution `z` therefore inverts the image of `s`. The proved center order
and quotient cardinality formula give order `2 * 2^n`; the dihedral recognition
theorem identifies this quotient from its relations and cardinality.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

include P in
public theorem central_quotient_equiv :
    Nonempty ((S ⧸ Subgroup.center S) ≃* DihedralGroup (2 ^ n)) := by
  let q := QuotientGroup.mk' (Subgroup.center S)
  have hst : q P.s * q P.t = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff P.u).2 P.u_mem_center
  have ht : q P.t = (q P.s)⁻¹ := eq_inv_of_mul_eq_one_right hst
  have hgen : Subgroup.closure ({q P.s, q P.z} : Set (S ⧸ Subgroup.center S)) = ⊤ := by
    let H := Subgroup.closure ({q P.s, q P.z} : Set (S ⧸ Subgroup.center S))
    have hsH : q P.s ∈ H := Subgroup.subset_closure (by simp)
    have hzH : q P.z ∈ H := Subgroup.subset_closure (by simp)
    have he : (⊤ : Subgroup S) ≤ H.comap q := by
      rw [← P.generate]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hsH
      · change q P.t ∈ H
        rw [ht]
        exact H.inv_mem hsH
      · exact hzH
    apply top_unique
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) x
    exact he (Subgroup.mem_top y)
  have hcard : Nat.card (S ⧸ Subgroup.center S) = 2 * 2 ^ n := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [P.card, P.card_center] at hh
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n)
    rw [← hh, pow_add, Nat.mul_comm 2 n, pow_mul]
    ring
  apply dihedralGroup_equiv_of_relations (by positivity) (q P.s) (q P.z)
    (by rw [← map_pow, P.s_pow, map_one])
    (by rw [← map_pow, P.z_sq, map_one]) _ hgen hcard
  rw [← map_inv, ← map_mul, ← map_mul]
  have hconj : P.z * P.s * P.z⁻¹ = P.t := by simpa only [P.z_inv] using P.conj_s
  rw [hconj, ht]
end ABG.Wreathed.Presentation
