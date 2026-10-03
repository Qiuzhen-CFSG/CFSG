module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Reflections of an odd cyclic orbit

Suppose a cyclic odd-prime group acts on a set, and an ambient element
inverts its rotations while fixing one point. Any two points of that orbit
are interchanged by a rotation-conjugate of the ambient element. Choose a
square root of the product of the two rotations; conjugating by this
midpoint gives the desired symmetry.

This is the valid action argument underlying Stellmacher (3.6)(c), Journal
of Algebra 190 (1997), p. 22. The result deliberately retains the chosen
reflection's order: an involution in a quotient need not lift to an actual
involution. It applies equally to actions on points and on subgroups.
-/

open scoped IsMulCommutative

universe u v

public theorem exists_conjugate_reflection_swapping
    {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (R : Subgroup G) [Finite R] [IsCyclic R]
    {p : ℕ} (hR : IsPGroup p R) (hp : Odd p)
    (s : G) (z : X) (hsz : s • z = z)
    (hinv : ∀ r : R, s * (r : G) * s⁻¹ = ((r : G))⁻¹)
    (r₁ r₂ : R) :
    ∃ r : R,
      ((r : G) * s * (r : G)⁻¹) • ((r₁ : G) • z) = (r₂ : G) • z ∧
      ((r : G) * s * (r : G)⁻¹) • ((r₂ : G) • z) = (r₁ : G) • z := by
  classical
  let _ : CommGroup R := IsMulCommutative.instCommGroup
  obtain ⟨r, hr⟩ := (hR.powEquiv hp.coprime_two_right).surjective (r₁ * r₂)
  have hsq : r ^ 2 = r₁ * r₂ := hr
  have hact (u : R) : s • ((u : G) • z) = ((u : G)⁻¹) • z := by
    have heq : s * (u : G) = (u : G)⁻¹ * s := by
      calc
        s * (u : G) = (s * (u : G) * s⁻¹) * s := by group
        _ = (u : G)⁻¹ * s := by rw [hinv u]
    rw [← mul_smul, heq, mul_smul, hsz]
  have hswap (u v : R) (huv : r ^ 2 = u * v) :
      ((r : G) * s * (r : G)⁻¹) • ((u : G) • z) = (v : G) • z := by
    have heq : r * (r⁻¹ * u)⁻¹ = v := by
      calc
        r * (r⁻¹ * u)⁻¹ = r ^ 2 * u⁻¹ := by
          simp [mul_inv_rev, pow_two, mul_assoc, mul_comm]
        _ = v := by rw [huv]; simp [mul_assoc]
    calc
      ((r : G) * s * (r : G)⁻¹) • ((u : G) • z) =
          (r : G) • (s • (((r⁻¹ * u : R) : G) • z)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      _ = (r : G) • ((((r⁻¹ * u : R) : G)⁻¹) • z) := by rw [hact]
      _ = (((r * (r⁻¹ * u)⁻¹ : R) : G)) • z := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      _ = (v : G) • z := by rw [heq]
  exact ⟨r, hswap r₁ r₂ hsq, hswap r₂ r₁ (by simpa [mul_comm] using hsq)⟩

