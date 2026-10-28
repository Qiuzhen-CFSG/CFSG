module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
/-!
# The full fixer of a symplectic root hyperplane

A subgroup of order q with one-dimensional natural displacement is the
whole pointwise fixer of its fixed hyperplane. Orthogonality bounds the
fixer's displacement by one, so the displacement-operator embedding bounds
its order by q; the original subgroup already has that order.

This is the root-fixer calculation used in the symplectic branch of
Meierfrankenfeld--Stellmacher (1993), (3.4), printed p.868.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]
theorem root_fixedSpace_fixer_eq (A : Subgroup (Sp F))
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hc : Nat.card A = Nat.card F) :
    fixingSubgroup (Sp F) (TwoLocalCover.fixedSpace A : Set (Vector F)) = A := by
  let B := fixingSubgroup (Sp F) (TwoLocalCover.fixedSpace A : Set (Vector F))
  have hAB : A ≤ B := by
    intro g hg
    exact (mem_fixingSubgroup_iff _).mpr (fun v hv => hv g hg)
  have hf : TwoLocalCover.fixedSpace A ≤ TwoLocalCover.fixedSpace B := by
    intro v hv g hg
    exact (mem_fixingSubgroup_iff _).mp hg v hv
  have hdim := Submodule.finrank_mono hf
  rw [←orthogonal_displacementSpace A,←orthogonal_displacementSpace B,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hd] at hdim
  have hle := (displacementSpace B).finrank_le
  have hB : Module.finrank F (displacementSpace B) ≤ 1 := by omega
  have hb : Nat.card B ≤ Nat.card F := by
    calc
      Nat.card B ≤ Nat.card F ^ (Module.finrank F (displacementSpace B))^2 :=
        card_actor_le_displacement_dimension B
      _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right Nat.card_pos (by nlinarith)
      _ = Nat.card F := pow_one _
  exact (Subgroup.eq_of_le_of_card_ge hAB (by rwa [hc])).symm
end Theory.SpecificGroups.SymplecticFour
