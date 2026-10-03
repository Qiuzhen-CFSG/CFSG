module
public import Theory.SpecificGroups.Quaternion.CentralTwoTriple

/-!
# Quaternion relations from an order-three conjugation orbit

If t has cube one and the square of x^-1*t*x*t^-1 belongs to a central
two-subgroup, this commutator and its adjusted conjugate satisfy the
quaternion presentation and the binary tetrahedral action identities.
No exact element order or nontriviality of the square is needed.

The three t-conjugates telescope to product one and have the same central
square. CentralTwoTriple supplies the quaternion relation; elementary
rearrangements give the generator pair matching the order-three action.
This is the arbitrary-kernel calculation in the q=3 Schur-cover step of
ABG II.3 Proposition 2.
-/

public section
namespace QuaternionGroup

theorem relations_of_central_two_orbit {E : Type*} [Group E]
    (Z : Subgroup E) (hZcenter : Z ≤ Subgroup.center E) (hZtwo : IsPGroup 2 Z)
    (x t : E) (ht : t ^ 3 = 1)
    (hs : (x⁻¹ * t * x * t⁻¹) ^ 2 ∈ Z) :
    let a := x⁻¹ * t * x * t⁻¹
    let b := (t * a * t⁻¹) * a⁻¹
    a ^ 4 = 1 ∧ b ^ 2 = a ^ 2 ∧ b * a = a⁻¹ * b ∧
      t * a * t⁻¹ = b * a ∧ t * b * t⁻¹ = a⁻¹ := by
  let a := x⁻¹ * t * x * t⁻¹
  let u := t * a * t⁻¹
  let v := t * u * t⁻¹
  have hscomm (y : E) : Commute (a ^ 2) y :=
    (Subgroup.mem_center_iff.mp (hZcenter hs) y).symm
  have hu2 : u ^ 2 = a ^ 2 := by
    calc
      u ^ 2 = t * a ^ 2 * t⁻¹ := by dsimp [u]; simp only [pow_two]; group
      _ = a ^ 2 := by rw [← (hscomm t).eq]; group
  have hv2 : v ^ 2 = a ^ 2 := by
    calc
      v ^ 2 = t * u ^ 2 * t⁻¹ := by dsimp [v]; simp only [pow_two]; group
      _ = a ^ 2 := by rw [hu2, ← (hscomm t).eq]; group
  have hauv : a * u * v = 1 := by
    calc
      a * u * v = x⁻¹ * t ^ 3 * x * (t ^ 3)⁻¹ := by
        dsimp [v, u, a]
        simp only [pow_succ, pow_zero]
        group
      _ = 1 := by rw [ht]; group
  obtain ⟨ha4, hua⟩ := quaternion_relations_of_central_two_triple
    Z hZcenter hZtwo a u v (a ^ 2) hs rfl hu2 hv2 hauv
  have hua' : u * a⁻¹ = a * u := by
    have h := congrArg (fun y : E => a * y * a⁻¹) hua
    simpa [mul_assoc] using h.symm
  have hui : u⁻¹ * a⁻¹ = a * u⁻¹ := by
    have h := congrArg (fun y : E => u⁻¹ * y * u⁻¹) hua
    simpa [mul_assoc] using h.symm
  change a ^ 4 = 1 ∧ (u * a⁻¹) ^ 2 = a ^ 2 ∧
    (u * a⁻¹) * a = a⁻¹ * (u * a⁻¹) ∧
    t * a * t⁻¹ = (u * a⁻¹) * a ∧
    t * (u * a⁻¹) * t⁻¹ = a⁻¹
  refine ⟨ha4, ?_, ?_, ?_, ?_⟩
  · calc
      (u * a⁻¹) ^ 2 = (u * a⁻¹) * (a * u) := by rw [pow_two, hua']
      _ = u ^ 2 := by rw [pow_two]; group
      _ = a ^ 2 := hu2
  · calc
      (u * a⁻¹) * a = u := by group
      _ = a⁻¹ * (u * a⁻¹) := by rw [hua']; group
  · dsimp [u]
    group
  · have hv : v = (a * u)⁻¹ := eq_inv_of_mul_eq_one_right hauv
    calc
      t * (u * a⁻¹) * t⁻¹ = v * u⁻¹ := by dsimp [v, u]; group
      _ = u⁻¹ * a⁻¹ * u⁻¹ := by rw [hv, mul_inv_rev]
      _ = a * u⁻¹ * u⁻¹ := by rw [hui]
      _ = a * (u ^ 2)⁻¹ := by group
      _ = a⁻¹ := by rw [hu2]; group

end QuaternionGroup
