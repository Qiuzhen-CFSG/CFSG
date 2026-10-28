module

public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Solvable normal subgroups of the native M₂₃ heptad stabilizer

The genuine quotient map onto A₇ sends a normal solvable subgroup to a
normal solvable subgroup. Simplicity and perfectness of A₇ force that image
to be trivial. Thus the original subgroup lies in the pointwise kernel of
order sixteen, and its order cannot be divisible by nine.

Source: GLS3, Table 5.3d, printed p.265; Aschbacher--Smith, the local
inspection in 15.3.41--42, printed p.1138. The quotient map and its kernel
are constructed in `HeptadStructure.SplitExtension`.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals

/-- Solvable normal subgroups of the heptad stabilizer lie in its actual
pointwise kernel, not just in a subgroup with the expected order. -/
theorem heptad_normal_solvable_le_kernel
    (N : Subgroup heptadStabilizer) [N.Normal] [Group.IsSolvable N] :
    N ≤ heptadKernel := by
  let f := heptadAlternatingAction
  have hf : Function.Surjective f :=
    fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩
  let D := N.map f
  let : D.Normal := (inferInstance : N.Normal).map f hf
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  have hD : D = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (α := Fin 7) (by simp) (N := D) with h | h
    · exact h
    · let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      let : Group.IsSolvable (alternatingGroup (Fin 7)) :=
        Group.isSolvable_of_surjective (f := D.subtype)
          (by rw [h]; exact topEquiv.surjective)
      exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7)) inferInstance).elim
  rw [← heptadAlternatingAction_ker]
  intro x hx
  exact mem_bot.mp (hD ▸ mem_map_of_mem f hx)

/-- The heptad candidate cannot contain a solvable normal seed of order
divisible by nine. -/
theorem heptad_normal_solvable_not_nine
    (N : Subgroup heptadStabilizer) [N.Normal] [Group.IsSolvable N] :
    ¬ 9 ∣ Nat.card N := by
  intro h9
  have h := h9.trans (card_dvd_of_le (heptad_normal_solvable_le_kernel N))
  rw [heptadKernel_card] at h
  norm_num at h

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals
