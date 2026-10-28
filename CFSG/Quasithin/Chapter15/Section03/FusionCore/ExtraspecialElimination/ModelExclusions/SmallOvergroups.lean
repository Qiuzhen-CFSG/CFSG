module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# The smaller-overgroup reduction in 15.3.49

An overgroup with quotient `S₃ × S₃` is solvable: its two-core is nilpotent
and its quotient is solvable. Thus conclusion (j) places it in `M ∩ H`.
Once the `L₃(2)` reduction is available, every member of the specified
small-overgroup family lies in `M`. Generation by that family is then
incompatible with `H` being outside `M`.

The generation theorem and the `L₃(2)` reduction are explicit remaining
inputs, not conclusions asserted by this module. The former requires the
binary parabolic geometry, and the latter the point-stabilizer module
calculation with its transported strong offender.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1144–1145, (j) and the `L₄(2), L₅(2)` paragraph.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

/-- No solvability assumption on the whole overgroup is needed: it follows
from the literal quotient identification and its actual two-core. -/
theorem solvable_of_symmetric_three_product_quotient (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Group.IsSolvable K := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetric_three_solvable
  have hquot : Group.IsSolvable (K ⧸ pCore 2 K) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let _ : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr ⟨inferInstance, hquot⟩

/-- Clause (j) discharges the `S₃ × S₃` branch of every smaller overgroup. -/
theorem symmetric_three_product_overgroup_le {H M L Y₀ T K : Subgroup G}
    (d : ReducedLocalData H M L Y₀ T)
    (hYK : Y₀ ⊔ T ≤ K) (hKH : K ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    K ≤ M ⊓ H :=
  d.solvable_overgroups K hYK hKH (solvable_of_symmetric_three_product_quotient K e)

/-- The final containment argument once the geometric generation and the
point-stabilizer reduction for the smaller `L₃(2)` quotients have been proved. -/
theorem exclude_by_small_overgroups {H M L Y₀ T : Subgroup G}
    (d : ReducedLocalData H M L Y₀ T)
    (hgen : H ≤ sSup (smallOvergroups H Y₀ T))
    (hthree : ∀ K : Subgroup G, Y₀ ⊔ T ≤ K → K ≤ H →
      Nonempty ((K ⧸ pCore 2 K) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) → K ≤ M) : False := by
  apply d.outside
  apply hgen.trans
  apply sSup_le
  rintro K ⟨hYK, hKH, hquot⟩
  change _ ∨ _ at hquot
  rcases hquot with htwo | hthreeK
  · obtain ⟨e⟩ := htwo
    exact (symmetric_three_product_overgroup_le d hYK hKH e).trans inf_le_left
  · exact hthree K hYK hKH hthreeK

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
