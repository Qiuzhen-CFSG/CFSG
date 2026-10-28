module

public import Theory.SpecificGroups.SL3.SplitMonomial.InvariantBasis
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable


/-!
# Geometric inputs for the full inverse image in SL₃

The full inverse image of a solvable projective subgroup is solvable: its
kernel is central. A nonabelian three-subgroup lifts to a nonabelian
three-group because the scalar center has order dividing three. A full
ambient Sylow two-subgroup also lifts into the inverse image. No order or
exponent of a chosen projective three-subgroup is imposed on its preimage.

These facts allow the same linear geometric argument to handle SL₃ and PSL₃.
Source: GLS3, proof of Theorem 6.5.3, passage from H to its full preimage Ĥ,
`refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SL3.SplitMonomial
variable {F : Type*} [Field F] [Finite F]

/-- The central kernel is a three-group and is retained in the preimage. -/
theorem projectivePreimage_three_group (U : Subgroup PSL(3,F)) (hU : IsPGroup 3 U) :
    IsPGroup 3 (projectivePreimage U) := by
  apply hU.comap_of_ker_isPGroup
  rw [QuotientGroup.ker_mk']
  exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using card_center_dvd_three F)

omit [Finite F] in
/-- An abelian preimage would have abelian projective image. -/
theorem projectivePreimage_noncommutative (U : Subgroup PSL(3,F))
    (hU : ¬ IsMulCommutative U) : ¬ IsMulCommutative (projectivePreimage U) := by
  intro ha
  let _ := ha
  apply hU
  let f : projectivePreimage U →* U := (PSL3.projection F).subgroupComap U
  have hf : Function.Surjective f :=
    (PSL3.projection F).subgroupComap_surjective_of_surjective U (PSL3.projection_surjective F)
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, mul_comm a b]

omit [Finite F] in
/-- A central extension of a solvable subgroup remains solvable. -/
theorem projectivePreimage_solvable (H : Subgroup PSL(3,F)) [Group.IsSolvable H] :
    Group.IsSolvable (projectivePreimage H) := by
  let f : projectivePreimage H →* H := (PSL3.projection F).subgroupComap H
  have hk : f.ker ≤ Subgroup.center (projectivePreimage H) := by
    intro x hx
    have hz : x.val ∈ Subgroup.center SL(3,F) := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext
      (Subgroup.mem_center_iff.mp hz y.val))
  let _ : Group.IsSolvable f.ker :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hk)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [Subgroup.range_subtype])

/-- A full ambient Sylow two-subgroup lifts into the full inverse image. -/
theorem exists_sylow_le_projectivePreimage
    (T : Sylow 2 PSL(3,F)) (H : Subgroup PSL(3,F)) (hT : (T : Subgroup _) ≤ H) :
    ∃ S : Sylow 2 SL(3,F), (S : Subgroup _) ≤ projectivePreimage H := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective
    (PSL3.projection_surjective F) 2 T
  refine ⟨S, ?_⟩
  change S.toSubgroup ≤ H.comap (PSL3.projection F)
  apply Subgroup.map_le_iff_le_comap.mp
  calc
    S.toSubgroup.map (PSL3.projection F) =
        (S.mapSurjective (PSL3.projection_surjective F) : Subgroup _) := rfl
    _ = T := congrArg Sylow.toSubgroup hS
    _ ≤ H := hT

/-- Lift precisely the nonabelian three-subgroup needed by the linear argument. -/
theorem projectivePreimage_nonabelian_three_subgroup (H : Subgroup PSL(3,F))
    (h : ∃ U : Subgroup PSL(3,F), U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    ∃ U : Subgroup SL(3,F), U ≤ projectivePreimage H ∧
      IsPGroup 3 U ∧ ¬ IsMulCommutative U := by
  obtain ⟨U, hUH, hU, hn⟩ := h
  exact ⟨projectivePreimage U, Subgroup.comap_mono hUH,
    projectivePreimage_three_group U hU, projectivePreimage_noncommutative U hn⟩
end Matrix.SL3.SplitMonomial
