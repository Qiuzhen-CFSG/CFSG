/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
The elementary conjugation proof is adapted from ATLAS
`Atlas/LinearGroups/Orthogonal/ElementaryNormal.lean`.
Revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Adaptation: CFSG isometry carriers, namespaces, and an explicit membership
lemma in place of the global normality instance.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.Coordinates
import Mathlib.Tactic

/-!
# Squared diagonal tori in the Siegel-generated group

A coroot scales two hyperbolic pairs inversely. Conjugating it by the swap on
one pair reverses that pair's multiplier; their product scales just the other
pair by a square. The Siegel-generated subgroup is normal in the full isometry
group, so both factors belong to it. Multiplying over all pairs puts every
squared diagonal in the exact elementary carrier, including split rank three.
This is a coordinate proof of the torus membership needed for the quasithin
A.2.18 obstruction (printed p.40); see also GLS3 §2.7.
-/

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
variable {F : Type u} [Field F] {r : ℕ}
/-- The Siegel-generated group is invariant under actual quadratic isometries. -/
theorem elementary_conj_mem {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g x : quadraticIsometrySubgroup Q)
    (hx : x ∈ elementarySubgroup Q) : g * x * g⁻¹ ∈ elementarySubgroup Q := by
  let gi : Q.IsometryEquiv Q :=
    { toLinearEquiv := g.val
      map_app' := (mem_quadraticIsometrySubgroup Q _).mp g.property }
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, hu, huv, rfl⟩ := hx
    have he : g * siegelElement Q u v hu huv * g⁻¹ =
        siegelElement Q (gi u) (gi v) ((gi.map_app u).trans hu)
          ((Quadratic.isometry_polar Q gi u v).trans huv) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      change gi (Quadratic.siegel Q u v (gi.symm w)) =
        Quadratic.siegel Q (gi u) (gi v) w
      rw [Quadratic.siegel_covariant, gi.apply_symm_apply]
    rw [he]
    exact siegelElement_mem _ _ _ _ _
  | one => simp
  | mul x y _ _ ihx ihy =>
    have he : g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group
    rw [he]
    exact (elementarySubgroup Q).mul_mem ihx ihy
  | inv x _ ih =>
    have he : g * x⁻¹ * g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [he]
    exact (elementarySubgroup Q).inv_mem ih

def flipOneLinear (j : Fin r) : VectorD r F ≃ₗ[F] VectorD r F where
  toFun x := Sum.elim (fun i => if i = j then x (.inr i) else x (.inl i))
    (fun i => if i = j then x (.inl i) else x (.inr i))
  invFun x := Sum.elim (fun i => if i = j then x (.inr i) else x (.inl i))
    (fun i => if i = j then x (.inl i) else x (.inr i))
  left_inv x := by funext i; cases i <;> dsimp <;> split_ifs <;> rfl
  right_inv x := by funext i; cases i <;> dsimp <;> split_ifs <;> rfl
  map_add' x y := by funext i; cases i <;> dsimp <;> split_ifs <;> rfl
  map_smul' a x := by funext i; cases i <;> dsimp <;> split_ifs <;> rfl

def flipOne (j : Fin r) : O r F := ⟨flipOneLinear j,
  (mem_quadraticIsometrySubgroup _ _).mpr (by
    intro x
    simp only [formD_apply, flipOneLinear, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mul_comm])⟩

@[simp] theorem flipOne_inv (j : Fin r) : (flipOne (F := F) j)⁻¹ = flipOne j := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

@[simp] theorem flipOne_left (j : Fin r) (x : VectorD r F) (i : Fin r) :
    (flipOne (F := F) j).val x (.inl i) = if i = j then x (.inr i) else x (.inl i) := rfl
@[simp] theorem flipOne_right (j : Fin r) (x : VectorD r F) (i : Fin r) :
    (flipOne (F := F) j).val x (.inr i) = if i = j then x (.inl i) else x (.inr i) := rfl

theorem single_square_diagonal {i j : Fin r} (hij : i ≠ j) (t : Fˣ) :
    diagonal (Pi.mulSingle i (t ^ 2)) =
      diagonal (pairEntries i j t) *
        (flipOne j * diagonal (pairEntries i j t) * (flipOne j)⁻¹) := by
  rw [flipOne_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext k
  cases k with
  | inl k =>
    change (diagonal (F := F) (Pi.mulSingle i (t ^ 2))).val x (.inl k) = (diagonal (pairEntries i j t)).val
      ((flipOne (F := F) j).val ((diagonal (pairEntries i j t)).val ((flipOne (F := F) j).val x))) (.inl k)
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pairEntries, hi, hj, hij, hij.symm, Pi.mulSingle_apply, pow_two, mul_assoc]
  | inr k =>
    change (diagonal (F := F) (Pi.mulSingle i (t ^ 2))).val x (.inr k) = (diagonal (pairEntries i j t)).val
      ((flipOne (F := F) j).val ((diagonal (pairEntries i j t)).val ((flipOne (F := F) j).val x))) (.inr k)
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pairEntries, hi, hj, hij, hij.symm, Pi.mulSingle_apply, pow_two, mul_assoc]

theorem single_square_mem_elementary {i j : Fin r} (hij : i ≠ j) (t : Fˣ) :
    diagonal (Pi.mulSingle i (t ^ 2)) ∈ elementarySubgroup (formD r F) := by
  rw [single_square_diagonal hij]
  exact (elementarySubgroup (formD r F)).mul_mem (pair_diagonal_mem hij t)
    (elementary_conj_mem _ _ _ (pair_diagonal_mem hij t))

theorem diagonal_square_mem_elementary (hr : 2 ≤ r) (d : Fin r → Fˣ) :
    diagonal (d ^ 2) ∈ elementarySubgroup (formD r F) := by
  have hsingle (i : Fin r) : diagonal (Pi.mulSingle i ((d i) ^ 2)) ∈
      elementarySubgroup (formD r F) := by
    let j : Fin r := if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with h
      · subst i
        exact Fin.ne_of_val_ne (by simp)
      · exact h
    exact single_square_mem_elementary hij (d i)
  have he : d ^ 2 = ∏ i : Fin r, Pi.mulSingle i ((d i) ^ 2) := by
    funext j
    simp [Finset.prod_apply, Pi.mulSingle_apply]
  change d ^ 2 ∈ (elementarySubgroup (formD r F)).comap diagonalHom
  rw [he]
  exact Subgroup.prod_mem _ (fun i _ => hsingle i)

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks
