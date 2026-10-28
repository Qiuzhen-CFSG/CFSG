module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Contracts

/-!
# The order-six obstruction in Held's crossing centralizer

In C2 x S3, a noncommuting pair of elements with square one has product
whose cube is either one or the unique nonidentity central element. This
finite assertion is kernel checked and transported through an actual
multiplicative equivalence. Commuting involutions whose product has cube
one must coincide.

Together these facts exclude order six for Held's mu*sigma: both factors
commute with delta, whereas xi and delta are distinct involutions with
product of order three. This module proves only the two group-theoretic
steps; LocalGeometry applies them to the full ambient crossing centralizer.
Source: D. Held, Illinois J. Math. 13 (1969), pp.238--239, Lemma 5.11,
DOI 10.1215/ijm/1256053756.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry

private def crossingZ : CrossingModel := (Multiplicative.ofAdd 1, 1)

private theorem crossing_center : ∀ z : CrossingModel,
    (∀ g, z * g = g * z) → z = 1 ∨ z = crossingZ := by decide +kernel

set_option synthInstance.maxSize 512 in
private theorem crossing_cube_choice : ∀ a b : CrossingModel,
    a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
    (a * b) ^ 3 = 1 ∨ (a * b) ^ 3 = crossingZ := by decide +kernel

public theorem cube_eq_one_or_central {H : Type*} [Group H]
    (e : H ≃* CrossingModel) {a b z : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : ¬ Commute a b)
    (hz : ∀ g, Commute z g) (hz1 : z ≠ 1) :
    (a * b) ^ 3 = 1 ∨ (a * b) ^ 3 = z := by
  have hez : e z = crossingZ := by
    rcases crossing_center (e z) (fun g => by
      simpa using congrArg e (hz (e.symm g)).eq) with h | h
    · exact (hz1 (e.injective (h.trans (map_one e).symm))).elim
    · exact h
  have hea : e a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have heb : e b ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  have heab : e a * e b ≠ e b * e a := by
    intro h
    exact hab (e.injective (by simpa using h))
  rcases crossing_cube_choice (e a) (e b) hea heb heab with h | h
  · exact Or.inl (e.injective (by simpa using h))
  · exact Or.inr (e.injective (by simpa [hez] using h))

public theorem involutions_eq_of_commute_of_product_cube {G : Type*} [Group G]
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : Commute a b) (h3 : (a * b) ^ 3 = 1) : a = b := by
  have h2 : (a * b) ^ 2 = 1 := by rw [hab.mul_pow, ha, hb, mul_one]
  apply mul_right_cancel (b := b)
  calc
    a * b = (a * b) ^ 3 := by rw [pow_succ, h2, one_mul]
    _ = 1 := h3
    _ = b * b := (pow_two b ▸ hb).symm

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
