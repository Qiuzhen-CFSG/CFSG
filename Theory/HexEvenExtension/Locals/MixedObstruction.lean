module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# The two order-48 local models are distinct

C₂ × S₄ has nine elements whose cube is one, whereas S₃ × D₈ has three.
These small kernel-checked counts are invariant under group isomorphism.
This separates the good and mixed local models in F.6.18(8–9), p.310.
-/
public noncomputable section
namespace Theory.HexEvenExtension.Locals
private theorem good_cube_card :
    Nat.card {x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem mixed_cube_card :
    Nat.card {x : Equiv.Perm (Fin 3) × DihedralGroup 4 // x ^ 3 = 1} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The good order-48 model cannot be the mixed S₃ × D₈ model. -/
theorem not_c2_symmetric_four_equiv_mixed :
    ¬ Nonempty ((Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ≃*
      (Equiv.Perm (Fin 3) × DihedralGroup 4)) := by
  rintro ⟨e⟩
  let j : {x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) // x ^ 3 = 1} ≃
      {x : Equiv.Perm (Fin 3) × DihedralGroup 4 // x ^ 3 = 1} :=
    e.toEquiv.subtypeEquiv (fun x => by
      change x ^ 3 = 1 ↔ (e x) ^ 3 = 1
      rw [← map_pow, e.map_eq_one_iff])
  have hc := Nat.card_congr j
  rw [good_cube_card, mixed_cube_card] at hc
  omega
end Theory.HexEvenExtension.Locals
