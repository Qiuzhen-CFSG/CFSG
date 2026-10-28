module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.PSL3Two.SourceFlag

/-!
# Generation and plane movement for the binary residual flag

The two residuals contain the three upper triangular root groups. Multiplying
cubic Levi elements by these roots gives both simple reflections; the existing
Bruhat theorem therefore gives the full matrix group. For movement, three
explicit displacements give the first basis vector, the third basis vector,
and the sum of the second and third, hence generate the whole natural module.
Only fixed matrices and eight vectors are checked computationally.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), pp.849,1009.
-/

public section

open Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
private theorem upper_four_line : Bruhat.upper 4 ∈ lineA := by decide +kernel
private theorem upper_zero : Bruhat.upper 0 = 1 := by decide +kernel
private theorem upper_last_line (j : Fin 2) : Bruhat.upper ⟨4 * j, by omega⟩ ∈ lineA := by
  fin_cases j
  · change Bruhat.upper 0 ∈ lineA
    rw [upper_zero]
    exact lineA.one_mem
  · exact upper_four_line

private theorem cubic_upper_four : cubic * Bruhat.upper 4 = Bruhat.perm 1 := by
  decide +kernel
private theorem diagram_cubic_upper_one : diagram cubic * Bruhat.upper 1 = Bruhat.perm 2 := by
  decide +kernel

private theorem borel_le_of_marks (H : Subgroup SL) (hp : pointA ≤ H)
    (hl : lineA ≤ H) : borelSL ≤ H := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := SourceFlag.borel_factors x hx
  have hi : Bruhat.upper ⟨i, by omega⟩ ∈ H := by
    apply hp
    apply pointV_le
    exact SourceFlag.upper_first i
  have hj : Bruhat.upper ⟨4 * j, by omega⟩ ∈ H := hl (upper_last_line j)
  exact H.mul_mem hi hj

private theorem reflections_mem_of_marks (H : Subgroup SL) (hp : pointA ≤ H)
    (hl : lineA ≤ H) : Bruhat.perm 1 ∈ H ∧ Bruhat.perm 2 ∈ H := by
  have hd : diagram cubic ∈ lineA :=
    (congrArg (fun S : Subgroup SL => diagram cubic ∈ S) pointA_map_diagram).mp
      ⟨cubic, cubic_mem, rfl⟩
  have hcH : cubic ∈ H := @hp cubic cubic_mem
  have huH : Bruhat.upper 4 ∈ H := @hl (Bruhat.upper 4) upper_four_line
  have hdH : diagram cubic ∈ H := @hl (diagram cubic) hd
  have htH : Bruhat.upper 1 ∈ H := @hp (Bruhat.upper 1) translations_mem.1
  have h₁ : Bruhat.perm 1 ∈ H := (congrArg (fun x : SL => x ∈ H) cubic_upper_four).mp
    (H.mul_mem (x := cubic) (y := Bruhat.upper 4) hcH huH)
  have h₂ : Bruhat.perm 2 ∈ H := (congrArg (fun x : SL => x ∈ H) diagram_cubic_upper_one).mp
    (H.mul_mem (x := diagram cubic) (y := Bruhat.upper 1) hdH htH)
  exact ⟨h₁, h₂⟩

/-- The two compatible parabolic residuals generate the full matrix group. -/
theorem residuals_generate : pointA ⊔ lineA = ⊤ :=
  Bruhat.eq_top (pointA ⊔ lineA)
    (borel_le_of_marks (pointA ⊔ lineA) le_sup_left le_sup_right)
    (reflections_mem_of_marks (pointA ⊔ lineA) le_sup_left le_sup_right).1
    (reflections_mem_of_marks (pointA ⊔ lineA) le_sup_left le_sup_right).2

private def e0 : Model := Multiplicative.ofAdd ![1,0,0]
private def e1 : Model := Multiplicative.ofAdd ![0,1,0]
private def e2 : Model := Multiplicative.ofAdd ![0,0,1]

private theorem displacement_eq (a : SL) (b : Model) :
    b * (slAut a b)⁻¹ = Multiplicative.ofAdd (b.toAdd + -(a.val.mulVec b.toAdd)) := by
  apply Multiplicative.toAdd.injective
  change b.toAdd + -(slAut a b).toAdd = b.toAdd + -(a.val.mulVec b.toAdd)
  rw [slAut_apply]

/-- Plane displacements under the point residual generate the natural module. -/
theorem plane_movement (D : Subgroup Model)
    (hD : ∀ b ∈ plane, ∀ a ∈ pointA, b * (slAut a b)⁻¹ ∈ D) : D = ⊤ := by
  have hd (a : SL) (ha : a ∈ pointA) := hD e1 (by decide) a ha
  have h0 : e0 ∈ D := by
    have he : e1 * (slAut (Bruhat.upper 1) e1)⁻¹ = e0 := by
      rw [displacement_eq]
      decide +kernel
    exact he ▸ hd _ translations_mem.1
  have h2 : e2 ∈ D := by
    have he : e1 * (slAut (cubic ^ 2) e1)⁻¹ = e2 := by
      rw [displacement_eq]
      decide +kernel
    exact he ▸ hd _ (pointA.pow_mem cubic_mem 2)
  have h12 : e1 * e2 ∈ D := by
    have he : e1 * (slAut cubic e1)⁻¹ = e1 * e2 := by
      rw [displacement_eq]
      decide +kernel
    exact he ▸ hd _ cubic_mem
  have h1 : e1 ∈ D := (D.mul_mem_cancel_right h2).mp h12
  apply top_unique
  intro v _
  have he : ∀ v : Model, v = e0 ^ (v.toAdd 0).val * e1 ^ (v.toAdd 1).val *
      e2 ^ (v.toAdd 2).val := by decide +kernel
  rw [he v]
  exact D.mul_mem (D.mul_mem (D.pow_mem h0 _) (D.pow_mem h1 _)) (D.pow_mem h2 _)

end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag

