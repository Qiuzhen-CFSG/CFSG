module
public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Mathlib.GroupTheory.IsPerfect

/-!
# Two-cores in perfect subgroups of characteristic-two SL₂

A nontrivial normal two-subgroup is conjugate into the upper root group.
Its normalizer lies in the triangular Borel, which is solvable. Thus a
perfect subgroup has trivial two-core, and every homomorphism from a perfect
group into SL₂ kills the source two-core.

This supplies the rank-one kernel step for the symplectic row of
Aschbacher--Smith 2.4.25, printed p.543, without any Sylow-order bound.
-/

public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A perfect subgroup of characteristic-two SL₂ has no normal two-subgroup. -/
theorem perfect_subgroup_twoCore_eq_bot (R : Subgroup SL(2,F))
    [Group.IsPerfect R] : pCore 2 R = ⊥ := by
  by_contra hne
  let N := (pCore 2 R).map R.subtype
  obtain ⟨P, hNP⟩ := (pCore_isPGroup (p := 2) (G := R)).map R.subtype |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,F) P (upperUnipotentSylow F 2)
  let f : R →* SL(2,F) := (MulAut.conj g).toMonoidHom.comp R.subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.coe_injective
  let W := (pCore 2 R).map f
  have hWU : W ≤ upperUnipotent F := by
    calc
      W = N.map (MulAut.conj g).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ ≤ (P : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hNP
      _ = upperUnipotent F := by
        change (g • P : Sylow 2 SL(2,F)).toSubgroup = _
        rw [hg]
        rfl
  have hW : W ≠ ⊥ := fun h => hne (((pCore 2 R).map_eq_bot_iff_of_injective hf).mp h)
  have hfn : f.range ≤ Subgroup.normalizer (W : Set SL(2,F)) := by
    have h := Subgroup.le_normalizer_map (H := pCore 2 R) f
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h
  have hfb : f.range ≤ rankOneBorel F :=
    hfn.trans (normalizer_le_rankOneBorel_of_le_upperUnipotent W hWU hW)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable (rankOneBorel F) :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer
      2 F (by decide) (upperUnipotentSylow F 2)
  let : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hfb)
  let : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
    intro hh
    apply hW
    exact bot_unique ((Subgroup.map_le_range f _).trans_eq hh))
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

/-- A perfect source has trivial two-core image in the actual SL₂ matrices. -/
theorem perfect_hom_twoCore_le_ker {L : Type*} [Group L] [Group.IsPerfect L]
    (f : L →* SL(2,F)) : pCore 2 L ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (pCore 2 L).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 L).Normal).map f.rangeRestrict f.rangeRestrict_surjective,
      pCore_isPGroup.map f.rangeRestrict⟩
  rw [perfect_subgroup_twoCore_eq_bot f.range] at h
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique h)
  intro l hl
  exact congrArg Subtype.val (hk hl)
end Matrix.SpecialLinearGroup
