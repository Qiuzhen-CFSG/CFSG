module
public import Theory.SpecificGroups.SymmetricEight.SingularDisplacement
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Fixed-point-free actions of a covered dihedral Sylow

The two elementary four-subgroups in a dihedral group of order eight cover
all involutions. If their images in the deleted eight-point action are
fixed-point-free, then every nonidentity element is fixed-point-free: an
element of order four has an involutory square, and a fixed point for the
element would also be fixed by its square.
-/

public section
open Subgroup
namespace ClassicalOrthogonal.BinaryD3Comparison

theorem dihedral_fixedPointFree_of_two_involution_planes
    (d : DihedralGroup 4 →* Equiv.Perm (Fin 8))
    (A B : Subgroup (DihedralGroup 4))
    (hclass : ∀ x : DihedralGroup 4,
      x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4)
    (hcover : ∀ x : DihedralGroup 4, orderOf x = 2 → x ∈ A ∨ x ∈ B)
    (hfree : ∀ x : DihedralGroup 4, x ∈ A ∨ x ∈ B →
      ∀ i, d x i ≠ i) :
    ∀ x : DihedralGroup 4, x ≠ 1 → ∀ i, d x i ≠ i := by
  intro x hx i
  rcases hclass x with rfl | horder | horder
  · exact (hx rfl).elim
  · rcases hcover x horder with hxA | hxB
    · exact hfree x (Or.inl hxA) i
    · exact hfree x (Or.inr hxB) i
  · intro hfix
    have hsq : x ^ 2 ≠ 1 := by
      intro hs
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs
      rw [horder] at hdvd
      omega
    have hsqorder : orderOf (x^2) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      have hpow : x^4 = 1 := by
        simpa [horder] using pow_orderOf_eq_one x
      have hpow2 : (x^2)^2 = 1 := by
        simpa [← pow_mul] using hpow
      exact ⟨hpow2,hsq⟩
    rcases hcover (x^2) hsqorder with hxA | hxB
    · apply (hfree (x^2) (Or.inl hxA) i)
      rw [map_pow]
      change d x (d x i) = i
      simp only [hfix]
    · apply (hfree (x^2) (Or.inr hxB) i)
      rw [map_pow]
      change d x (d x i) = i
      simp only [hfix]

end ClassicalOrthogonal.BinaryD3Comparison
