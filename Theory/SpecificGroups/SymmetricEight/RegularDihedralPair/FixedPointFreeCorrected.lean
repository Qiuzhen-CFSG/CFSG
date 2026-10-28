module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.FixedPointFree
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Corrected fixed-point-free dihedral lemma

The fixed-point-free hypothesis is explicitly restricted to nonidentity elements;
the identity belongs to every subgroup and is of course not fixed-point-free.
-/

public section
open Subgroup
namespace ClassicalOrthogonal.BinaryD3Comparison

/-- A covered pair of elementary-four planes gives a fixed-point-free action of
all nonidentity elements once the order-two elements are fixed-point-free. -/
theorem dihedral_fixedPointFree_of_two_involution_planes_nontrivial
    (d : DihedralGroup 4 →* Equiv.Perm (Fin 8))
    (A B : Subgroup (DihedralGroup 4))
    (hclass : ∀ x : DihedralGroup 4,
      x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4)
    (hcover : ∀ x : DihedralGroup 4, orderOf x = 2 → x ∈ A ∨ x ∈ B)
    (hfree : ∀ x : DihedralGroup 4, x ≠ 1 → x ∈ A ∨ x ∈ B →
      ∀ i, d x i ≠ i) :
    ∀ x : DihedralGroup 4, x ≠ 1 → ∀ i, d x i ≠ i := by
  intro x hx i
  rcases hclass x with rfl | horder | horder
  · exact (hx rfl).elim
  · rcases hcover x horder with hxA | hxB
    · exact hfree x hx (Or.inl hxA) i
    · exact hfree x hx (Or.inr hxB) i
  · intro hfix
    have hsq : x ^ 2 ≠ 1 := by
      intro hs
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs
      rw [horder] at hdvd
      omega
    have hsqorder : orderOf (x ^ 2) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      have hpow : x ^ 4 = 1 := by
        simpa [horder] using pow_orderOf_eq_one x
      have hpow2 : (x ^ 2) ^ 2 = 1 := by
        simpa [← pow_mul] using hpow
      exact ⟨hpow2, hsq⟩
    rcases hcover (x ^ 2) hsqorder with hxA | hxB
    · apply (hfree (x ^ 2) (by exact hsq) (Or.inl hxA) i)
      rw [map_pow]
      change d x (d x i) = i
      simp only [hfix]
    · apply (hfree (x ^ 2) (by exact hsq) (Or.inr hxB) i)
      rw [map_pow]
      change d x (d x i) = i
      simp only [hfix]

end ClassicalOrthogonal.BinaryD3Comparison
