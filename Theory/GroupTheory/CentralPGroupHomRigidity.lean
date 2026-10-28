module
public import Theory.GroupTheory.PGroup.TrivialImage
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Homomorphism rigidity modulo a central finite p-subgroup

If a group has no normal subgroup of index prime p, two homomorphisms agree
whenever their pointwise discrepancy lies in a finite central p-subgroup of
the target. Neither the whole source nor the whole target need be finite.

Centrality makes the discrepancy a homomorphism into the given p-subgroup.
The proved trivial-image theorem for groups without normal index p forces
this homomorphism to be trivial, giving pointwise equality.

This supplies an action-comparison step in ABG II.3 Proposition 3, article
p.27: odd-field SL2 has no normal subgroup of index two and center of order
two. Thus the comparison holds even at field order three, where perfectness
is unavailable. The separate group-model extension and quotient-alignment
steps remain necessary.
-/

namespace MonoidHom

public theorem eq_of_central_pgroup_discrepancy
    {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ p)
    (Z : Subgroup H) [Finite Z] (hZ : Z ≤ Subgroup.center H) (hpZ : IsPGroup p Z)
    (f g : G →* H) (hd : ∀ x : G, f x * (g x)⁻¹ ∈ Z) : f = g := by
  let d : G →* Z := {
    toFun x := ⟨f x * (g x)⁻¹, hd x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := by
      apply Subtype.ext
      change f (x * y) * (g (x * y))⁻¹ =
        (f x * (g x)⁻¹) * (f y * (g y)⁻¹)
      have hc := Subgroup.mem_center_iff.mp (hZ (hd y)) (g x)⁻¹
      simp only [map_mul, mul_inv_rev]
      calc
        _ = f x * ((f y * (g y)⁻¹) * (g x)⁻¹) := by simp only [mul_assoc]
        _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := by rw [hc]
        _ = _ := by simp only [mul_assoc] }
  ext x
  have hx := eq_one_of_no_normal_index_prime hno hpZ d x
  have hval : f x * (g x)⁻¹ = 1 := congrArg Subtype.val hx
  exact mul_inv_eq_one.mp hval

end MonoidHom

