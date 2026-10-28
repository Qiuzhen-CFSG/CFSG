module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Odd subgroups inverted by elements of a normalized subgroup

If an odd subgroup `R` normalizes `F` and an element of `F` inverts `R`,
then `R ≤ F`. Indeed, every square in `R` is a commutator lying in `F`,
and squaring is surjective on a finite odd group. Inversion also forces
`R` to be abelian. Normality is required only relative to `R`.

These are the containment and commutativity steps in GLS, Volume 4,
Chapter 2, Proposition 16.5, before applying the linear model geometry.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- An odd subgroup inverted by an element of a subgroup it normalizes
is contained in that subgroup. The inverter need not have order two. -/
public theorem le_of_odd_inverted_of_le_normalizer (R F : Subgroup G)
    (hodd : Odd (Nat.card R)) (hnorm : R ≤ normalizer F)
    (t : G) (ht : t ∈ F) (hinv : ∀ x ∈ R, t * x * t⁻¹ = x⁻¹) : R ≤ F := by
  intro y hy
  obtain ⟨x, hx⟩ := hodd.coprime_two_right.pow_left_bijective.surjective (⟨y, hy⟩ : R)
  have hi : t * (x : G)⁻¹ * t⁻¹ = x := by
    simpa using hinv x⁻¹ (R.inv_mem x.property)
  have hsq : (x : G) ^ 2 ∈ F := by
    have heq : (x : G) ^ 2 = ((x : G) * t * (x : G)⁻¹) * t⁻¹ := by
      calc
        (x : G) ^ 2 = (x : G) * x := pow_two _
        _ = (x : G) * (t * (x : G)⁻¹ * t⁻¹) :=
          congrArg (fun z => (x : G) * z) hi.symm
        _ = _ := by simp only [mul_assoc]
    rw [heq]
    exact F.mul_mem ((mem_normalizer_iff.mp (hnorm x.property) t).mp ht) (F.inv_mem ht)
  simpa only [← Subgroup.coe_pow, hx] using hsq

/-- Elementwise inversion by conjugation forces a subgroup to be abelian. -/
public theorem isMulCommutative_of_inverted (R : Subgroup G) (t : G)
    (hinv : ∀ x ∈ R, t * x * t⁻¹ = x⁻¹) : IsMulCommutative R := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  have heq : ((x : G) * y)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ := by
    rw [← hinv _ (R.mul_mem x.property y.property), ← hinv _ x.property,
      ← hinv _ y.property]
    simp [mul_assoc]
  simpa using congrArg Inv.inv heq

end Subgroup
