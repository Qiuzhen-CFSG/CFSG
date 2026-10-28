module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Larger-field linear and Ree Borel containment

The concrete PSL₃ matrix calculation normalizes every Sylow subgroup in
a solvable overgroup. For the genuine Ree fixed group, align the supplied
Sylow with the positive roots, use the proved fixed-root containment, and
transport its normalizer back. Both arguments preserve the actual field
and model equivalence. They need no assumption about the later contradiction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the first
paragraph of the final proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
open Chapter1.Section02.LocalModels

variable {D : Type*} [Group D] [Finite D]

/-- The PSL₃ branch, including the field of order four. -/
theorem linear_control {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL D 3 (2 ^ n)) : ParabolicSolvableControl D := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply control_of_mulEquiv e
  intro U P H _hNP _hP _hHP hsol hUH
  exact Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F hn hF U H hsol hUH

/-- The genuine Ree branch at field order 2^(2m+1), for m positive. -/
theorem ree_control {m : ℕ} (hm : 1 ≤ m)
    (hmodel : IsReeF4At D m) : ParabolicSolvableControl D := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  apply control_of_mulEquiv (e.trans d.modelEquiv)
  intro U P H _hNP _hP _hHP hsol hUH
  obtain ⟨g, hg⟩ :=
    ReeF4.Parabolics.ThreeSylowContainment.exists_conjugate_eq_unipotent U
  let a := MulAut.conj g
  have hU : (U : Subgroup (ReeF4.Model m)).map a.toMonoidHom =
      ReeF4.Parabolics.unipotent m := hg
  let : Group.IsSolvable H := hsol
  have hsol' : Group.IsSolvable (H.map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective H)
  have hUH' : ReeF4.Parabolics.unipotent m ≤ H.map a.toMonoidHom := by
    rw [← hU]
    exact map_mono hUH
  have hN := (ReeF4.Parabolics.ThreeSylowContainment.le_borel_of_solvable
    hm _ hsol' hUH').trans (ReeF4.Parabolics.borel_le_unipotent_normalizer m)
  rw [← hU, ← map_equiv_normalizer_eq] at hN
  exact (map_le_map_iff_of_injective a.injective).mp hN

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
