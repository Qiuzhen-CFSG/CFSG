module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Algebra.Group.Prod

/-!
# The commuting choice in the small four-group normalizer

Inside S₄ × C₂, let d and b generate a dihedral group of order eight,
with central involution a = (db)². Two cube-one elements inverted by d
commute after possibly conjugating the second by a. The S₄ assertion is
a finite kernel calculation. Projection to S₄ and the abelian C₂ factor
then prove the assertion for every group actually isomorphic to this product.

The intended application to Held 5.1 is the normalizer of the marked
four-group in Aut(A₆), with d induced by mu-prime and b by tau*lambda.
Identifying that actual normalizer and transporting the actors are separate
obligations. No such ambient identification is assumed here.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 5.1, pp.235--236.
This is an alternative small-normalizer calculation for the commuting choice.
-/

open Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

set_option synthInstance.maxSize 32768 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem choice_four : ∀ d b : Perm (Fin 4),
    d ^ 2 = 1 → b ^ 2 = 1 →
    (d * b * d * b) ^ 2 = 1 → d * b * d * b ≠ 1 →
    ∀ u v : Perm (Fin 4), u ^ 3 = 1 → v ^ 3 = 1 →
      d * u * d = u⁻¹ → d * v * d = v⁻¹ →
      Commute u v ∨ Commute u ((d * b * d * b)⁻¹ * v * (d * b * d * b)) := by
  simp only [Commute, SemiconjBy]
  decide +kernel

/-- In the model S₄ × C₂, involution-inverted cube-one elements admit the
choice between v and v conjugated by the central involution of the marked D₈. -/
public theorem commuting_choice_in_symmetricFour_times_two
    {K : Type*} [Group K] (j : K ≃* (Perm (Fin 4) × Multiplicative (ZMod 2)))
    (u v d b : K) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hd : d ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha : (d * b * d * b) ^ 2 = 1) (hne : d * b * d * b ≠ 1)
    (hdu : d * u * d = u⁻¹) (hdv : d * v * d = v⁻¹) :
    Commute u v ∨ Commute u ((d * b * d * b)⁻¹ * v * (d * b * d * b)) := by
  let f : K →* Perm (Fin 4) := (MonoidHom.fst _ _).comp j.toMonoidHom
  have hsecond : (j (d * b * d * b)).2 = 1 := by
    have hc : ∀ r s : Multiplicative (ZMod 2), r * s * r * s = 1 := by decide +kernel
    rw [map_mul, map_mul, map_mul]
    exact hc (j d).2 (j b).2
  have hfirst : f d * f b * f d * f b ≠ 1 := by
    intro h
    apply hne
    apply j.injective
    apply Prod.ext
    · rw [map_one, map_mul, map_mul, map_mul]
      exact h
    · rw [map_one]
      exact hsecond
  have transfer (x y : K) (h : Commute (f x) (f y)) : Commute x y := by
    apply Commute.of_map j.injective
    exact Commute.prod h (Commute.all _ _)
  rcases choice_four (f d) (f b) (by simp only [← map_pow, hd, map_one])
      (by simp only [← map_pow, hb, map_one])
      (by simp only [← map_mul, ← map_pow, ha, map_one]) hfirst
      (f u) (f v) (by simp only [← map_pow, hu, map_one])
      (by simp only [← map_pow, hv, map_one])
      (by simpa only [← map_mul, ← map_inv] using congrArg f hdu)
      (by simpa only [← map_mul, ← map_inv] using congrArg f hdv) with h | h
  · exact Or.inl (transfer _ _ h)
  · apply Or.inr
    apply transfer
    simpa only [map_mul, map_inv] using h

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
