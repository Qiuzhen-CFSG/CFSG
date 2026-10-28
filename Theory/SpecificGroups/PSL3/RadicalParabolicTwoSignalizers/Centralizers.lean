module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Geometry

/-!
# Centralizers of the two radicals in PSL₃(5)

Commuting with the two coordinate root elements forces a matrix to be scalar
modulo the root plane. The determinant equation is r³ = 1, whose only solution
in the five-element field is r = 1. The faithful scalar projection therefore
gives C(P) = P for each radical P. A centralizing two-subgroup is consequently
trivial, by coprimality. Normalized two-subgroups require a further argument.

Source: the concrete parabolic geometry used in Aschbacher–Smith,
`refs/quasithin.pdf`, proof of 1.3.8, printed p.513.
-/

public section

open scoped MatrixGroups IsMulCommutative
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.RadicalParabolicTwoSignalizers

local notation "F" => ZMod 5

private theorem cube_one (x : F) (hx : x ^ 3 = 1) : x = 1 := by
  have h : ∀ y : ZMod 5, y ^ 3 = 1 → y = 1 := by decide
  exact h x hx

private theorem centralizes_point (g : SL(3,F))
    (h : ∀ a c : F, g * specialLinear F ⟨a,0,c⟩ = specialLinear F ⟨a,0,c⟩ * g) :
    g ∈ rootPlaneSL F true := by
  have entries (a c : F) (i j : Fin 3) :
      (g.val * matrix F ⟨a,0,c⟩) i j = (matrix F ⟨a,0,c⟩ * g.val) i j :=
    congrArg (fun x : SL(3,F) => x.val i j) (h a c)
  have h10 := entries 1 0 1 1
  have h20 := entries 1 0 2 1
  have h21 := entries 0 1 0 1
  have h12 := entries 1 0 0 2
  have h11 := entries 1 0 0 1
  have h22 := entries 0 1 0 2
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21 h12 h11 h22
  have h11 : g.val 0 0 = g.val 1 1 := add_right_cancel (h11.trans (add_comm _ _))
  have h22 : g.val 0 0 = g.val 2 2 := add_right_cancel (h22.trans (add_comm _ _))
  have h00 : g.val 0 0 = 1 := by
    apply cube_one
    have hd := g.property
    rw [Matrix.det_fin_three] at hd
    simp only [h10, h20, h21, h12, ← h11, ← h22] at hd
    simpa [pow_succ, mul_assoc] using hd
  apply (mem_rootPlaneSL_point F g).mpr
  refine ⟨g.val 0 1, g.val 0 2, ?_⟩
  apply Subtype.ext
  change matrix F _ = g.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, h10, h20, h21, h12, ← h11, ← h22, h00]

private theorem centralizes_line (g : SL(3,F))
    (h : ∀ b c : F, g * specialLinear F ⟨0,b,c⟩ = specialLinear F ⟨0,b,c⟩ * g) :
    g ∈ rootPlaneSL F false := by
  have entries (b c : F) (i j : Fin 3) :
      (g.val * matrix F ⟨0,b,c⟩) i j = (matrix F ⟨0,b,c⟩ * g.val) i j :=
    congrArg (fun x : SL(3,F) => x.val i j) (h b c)
  have h10 := entries 0 1 1 2
  have h20 := entries 0 1 2 2
  have h21 := entries 1 0 2 2
  have h01 := entries 1 0 0 2
  have h11 := entries 1 0 1 2
  have h00 := entries 0 1 0 2
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21 h01 h11 h00
  have h11 : g.val 1 1 = g.val 2 2 := add_right_cancel (h11.trans (add_comm _ _))
  have h00 : g.val 0 0 = g.val 2 2 := add_right_cancel (h00.trans (add_comm _ _))
  have h22 : g.val 2 2 = 1 := by
    apply cube_one
    have hd := g.property
    rw [Matrix.det_fin_three] at hd
    simp only [h10, h20, h21, h01, h11, h00] at hd
    simpa [pow_succ, mul_assoc] using hd
  apply (mem_rootPlaneSL_line F g).mpr
  refine ⟨g.val 1 2, g.val 0 2, ?_⟩
  apply Subtype.ext
  change matrix F _ = g.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, h10, h20, h21, h01, h11, h00, h22]

theorem centralizer_rootPlane (point : Bool) :
    centralizer (rootPlane F point : Set Model) = rootPlane F point := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := projection_surjective F x
    apply mem_map.mpr
    refine ⟨g, ?_, rfl⟩
    have hcomm (u : SL(3,F)) (hu : u ∈ rootPlaneSL F point) : g * u = u * g := by
      apply projection_injective
      simp only [map_mul]
      exact (hx _ (mem_map_of_mem (projection F) hu)).symm
    cases point
    · apply centralizes_line g
      intro b c
      exact hcomm _ ((mem_rootPlaneSL_line F _).mpr ⟨b,c,rfl⟩)
    · apply centralizes_point g
      intro a c
      exact hcomm _ ((mem_rootPlaneSL_point F _).mpr ⟨a,c,rfl⟩)
  · let : IsElementaryAbelian 5 (rootPlane F point) := rootPlane_elementary point
    intro x hx y hy
    exact congrArg (fun z : rootPlane F point => (z : Model))
      (mul_comm (⟨y,hy⟩ : rootPlane F point) ⟨x,hx⟩)

theorem centralizing_twoSubgroup_eq_bot (point : Bool) (S : Subgroup Model)
    (hS : IsPGroup 2 S)
    (hcentral : S ≤ centralizer (rootPlane F point : Set Model)) : S = ⊥ := by
  have hP : IsPGroup 5 (rootPlane F point) :=
    IsPGroup.of_card (n := 2) (card_rootPlane point)
  have hd := IsPGroup.disjoint_of_coprime hS hP (by decide : Nat.Coprime 2 5)
  rw [centralizer_rootPlane] at hcentral
  apply eq_bot_iff.mpr
  intro x hx
  exact mem_bot.mpr (Subgroup.disjoint_def.mp hd hx (hcentral hx))

end Matrix.PSL3.RadicalParabolicTwoSignalizers
