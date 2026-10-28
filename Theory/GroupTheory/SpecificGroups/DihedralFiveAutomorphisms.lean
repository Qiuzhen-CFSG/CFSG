module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic
/-!
# Automorphisms of the dihedral group of order ten

An automorphism is determined by a marked rotation and reflection. Their
images are respectively one of the four nonidentity rotations and one of
the five reflections, so the automorphism group has order at most twenty.
Only these small element calculations are enumerated, not the automorphisms.
The same generators show that the group is centerless.

These facts bound the actual quotient action in the dihedral branch of
DGS, *Groups and Graphs* (1985), 6.1, pp.118--119.
-/

public section
open Subgroup
namespace DihedralGroup
private theorem aut_ext_generators_five (a b : MulAut (DihedralGroup 5))
    (hr : a (r 1) = b (r 1)) (hs : a (sr 0) = b (sr 0)) : a = b := by
  ext x
  have hrot (i : ZMod 5) : a (r i) = b (r i) := by
    have he : (r i : DihedralGroup 5) = (r 1) ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, map_pow, hr]
  cases x with
  | r i => exact hrot i
  | sr i =>
    have he : (sr i : DihedralGroup 5) = sr 0 * r i := by simp
    rw [he, map_mul, map_mul, hs, hrot]

/-- The concrete order-ten dihedral group is centerless. -/
theorem five_center_eq_bot : center (DihedralGroup 5) = ⊥ := by
  apply bot_unique
  intro x hx
  exact (show ∀ x : DihedralGroup 5, (∀ y, y * x = x * y) → x = 1 by decide +kernel)
    x (mem_center_iff.mp hx)

/-- The rotation and reflection images give at most twenty automorphisms. -/
theorem card_mulAut_five_le_twenty : Nat.card (MulAut (DihedralGroup 5)) ≤ 20 := by
  let R := {x : DihedralGroup 5 // x ^ 5 = 1 ∧ x ≠ 1}
  let T := {x : DihedralGroup 5 // x ^ 2 = 1 ∧ x ≠ 1}
  let f : MulAut (DihedralGroup 5) → R × T := fun a =>
    (⟨a (r 1), by
      constructor
      · rw [←map_pow, show (r 1 : DihedralGroup 5)^5 = 1 by decide, map_one]
      · exact a.map_ne_one_iff.mpr (by decide)⟩,
     ⟨a (sr 0), by
      constructor
      · rw [←map_pow, show (sr 0 : DihedralGroup 5)^2 = 1 by decide, map_one]
      · exact a.map_ne_one_iff.mpr (by decide)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    exact aut_ext_generators_five a b
      (congrArg (fun p : R × T => p.1.val) hab)
      (congrArg (fun p : R × T => p.2.val) hab)
  have hc : Nat.card (R × T) = 20 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc
end DihedralGroup
