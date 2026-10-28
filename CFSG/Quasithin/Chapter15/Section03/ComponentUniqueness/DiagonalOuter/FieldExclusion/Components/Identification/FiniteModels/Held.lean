module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer

/-!
# The Held 2B component obstruction

The full centralizer of the marked 2B involution is the actual max5 subgroup.
Its normal two-core is self-centralizing. The component dichotomy therefore
places every proposed ordinary component in a two-group, which is impossible
for a nontrivial perfect group. The PSL₃(2) section in this row is not an
ordinary component.

This settles only the marked 2B row. Held's other inner row, its outer covering
row and abstract automorphism realization are separate remaining obligations.
Source: GLS3 Table 5.3p; Aschbacher–Smith, proof of 15.3.38, printed p.1137.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

open Held.TwoLocalCandidates Held.TwoLocalCandidates.Cores

/-- The actual max5 kernel action excludes all ordinary components. -/
theorem held_max5_no_component (D : Subgroup (subgroup 2)) :
    ¬ IsComponent (subgroup 2) D := by
  intro hD
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  let : (core 2).Normal := core_normal 2
  have hle : D ≤ core 2 := by
    rcases hD.normal_dichotomy (core 2) with h | h
    · exact h
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans max5_selfCentralizing
  let : Group.IsNilpotent D := ((core_isPGroup 2).to_le hle).isNilpotent
  exact Group.IsPerfect.not_isSolvable D inferInstance

/-- No ordinary component exists in the full marked 2B fixed subgroup. -/
theorem held_twoB_no_component
    (D : Subgroup (MulAut.conj (max5First ^ 4)).fixedSubgroup) :
    ¬ IsComponent (MulAut.conj (max5First ^ 4)).fixedSubgroup D := by
  let e : (MulAut.conj (max5First ^ 4)).fixedSubgroup ≃* max5 :=
    MulEquiv.subgroupCongr ((MulAut.fixedSubgroup_conj _).trans
      Held.InvolutionFixedData.TwoB.centralizer_eq_max5)
  intro hD
  exact held_max5_no_component (D.map e.toMonoidHom) (hD.map_equiv e)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
