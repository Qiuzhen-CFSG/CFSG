module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentGeneration
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Structural constraints on the source component stabilizer

The component stabilizer contains the full ambient Sylow two- and
three-subgroups, so its index is prime to six. It is nonsolvable because
it contains the original N(V), whose actual normalizer quotient is A₆.
These constraints retain the original subgroup when passing from local
incidence to the global recognition step.

Source: Aschbacher, *Sporadic Groups* (1994),45.5,45.9–45.11, pp.244,247–249.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem componentStabilizer_index_odd : Odd c.componentStabilizer.index := by
  obtain ⟨T, hT, -⟩ := c.exists_binarySylow_le_componentStabilizer
  exact Nat.not_even_iff_odd.mp (fun he => T.not_dvd_index
    (he.two_dvd.trans (index_dvd_of_le hT)))

theorem three_not_dvd_componentStabilizer_index : ¬3 ∣ c.componentStabilizer.index := by
  have hT : (c.sylow : Subgroup G) ≤ c.componentStabilizer :=
    ((c.sylow : Subgroup G).le_normalizer.trans (c.common_normalizer.le.trans inf_le_right)).trans
      c.point_normalizer_le_componentStabilizer
  exact fun hd => c.sylow.not_dvd_index (hd.trans (index_dvd_of_le hT))

theorem componentStabilizer_not_solvable : ¬Group.IsSolvable c.componentStabilizer := by
  intro hs
  let : Group.IsSolvable c.componentStabilizer := hs
  let : Group.IsSolvable (normalizer (c.V : Set G)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion c.kernel_normalizer_le_componentStabilizer)
      (inclusion_injective c.kernel_normalizer_le_componentStabilizer)
  let : Group.IsSolvable (NormalizerAction.Star c.V) := inferInstance
  obtain ⟨e⟩ := c.quotient_equiv_alternating_six
  let : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
