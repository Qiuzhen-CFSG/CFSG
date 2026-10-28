module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement

/-!
# Perfect normal subgroups of symplectic parabolics

A nonsolvable perfect subgroup normal in a nonbinary symplectic parabolic
lies in its determinant kernel. Its image in the simple SL₂ quotient is
nontrivial and hence full. The solvable kernel supplements it, so perfect
subnormal generation identifies it with the entire local residual.

This retains the literal point and plane embeddings used in C.4.8 and
Aschbacher--Smith 12.7.5, printed pp.154 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour

private theorem perfect_normal_eq_top_of_simple_image
    {A S : Type*} [Group A] [Finite A] [Group S] [IsSimpleGroup S]
    [Group.IsPerfect A] (q : A →* S) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (B : Subgroup A) [B.Normal] [Group.IsPerfect B]
    (hB : ¬ Group.IsSolvable B) : B = ⊤ := by
  let : (B.map q).Normal := (inferInstance : B.Normal).map q hq
  have himage : B.map q = ⊤ := by
    rcases (inferInstance : (B.map q).Normal).eq_bot_or_eq_top with hb | ht
    · have hle : B ≤ q.ker := (map_eq_bot_iff B).mp hb
      exact (hB (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))).elim
    · exact ht
  have hsup : B ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq, comap_top] using congrArg (comap q) himage
  exact ((inferInstance : B.Normal).isSubnormal.eq_solvableResidual_of_sup_eq_top
    q.ker hsup).trans solvableResidual_eq_top

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
include hcard hn

/-- A nonsolvable perfect normal subgroup of the actual point parabolic
is exactly its determinant-one local residual. -/
theorem perfect_normal_pointParabolic_eq_local (B : Subgroup (Sp F))
    [Group.IsPerfect B] (hB : ¬ Group.IsSolvable B)
    (hBP : B ≤ pointParabolic) (hPB : pointParabolic ≤ normalizer (B : Set (Sp F))) :
    B = pointLocal := by
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2 = 2 ^ 1 from rfl).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  have hBL : B ≤ pointLocal :=
    (le_map_solvableResidual_of_isPerfect B pointParabolic hBP).trans
      (pointParabolic_solvableResidual_eq hcard hn).le
  let B' := B.subgroupOf pointLocal
  let e := subgroupOfEquivOfLe hBL
  let : B'.Normal := normal_subgroupOf_of_le_normalizer (pointLocal_le.trans hPB)
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect (pointLocal (F := F)) := pointLocal_perfect hcard hn
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := NaturalExtension.model_simple hF
  let : Group.IsSolvable (pointQuotient (F := F)).ker := by
    rw [pointQuotient_ker, ← pointLocal_core_eq hcard hn]
    let : Group.IsNilpotent (pCore 2 (pointLocal (F := F))) := pCore_isPGroup.isNilpotent
    infer_instance
  have ht : B' = ⊤ := perfect_normal_eq_top_of_simple_image pointQuotient
    pointQuotient_surjective B' (fun hs => hB (by
      let := hs
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective))
  have hh := congrArg (map (pointLocal (F := F)).subtype) ht
  simpa only [B', map_subgroupOf_eq_of_le hBL, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- A nonsolvable perfect normal subgroup of the actual plane parabolic
is exactly its determinant-one local residual. -/
theorem perfect_normal_planeParabolic_eq_local (B : Subgroup (Sp F))
    [Group.IsPerfect B] (hB : ¬ Group.IsSolvable B)
    (hBP : B ≤ planeParabolic) (hPB : planeParabolic ≤ normalizer (B : Set (Sp F))) :
    B = planeLocal := by
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2 = 2 ^ 1 from rfl).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  have hBL : B ≤ planeLocal :=
    (le_map_solvableResidual_of_isPerfect B planeParabolic hBP).trans
      (planeParabolic_solvableResidual_eq hcard hn).le
  let B' := B.subgroupOf planeLocal
  let e := subgroupOfEquivOfLe hBL
  let : B'.Normal := normal_subgroupOf_of_le_normalizer (planeLocal_le.trans hPB)
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect (planeLocal (F := F)) := planeLocal_perfect hcard hn
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := NaturalExtension.model_simple hF
  let : Group.IsSolvable (Plane.quotientMap (F := F)).ker := by
    rw [Plane.quotientMap_ker, ← planeLocal_core_eq hcard hn]
    let : Group.IsNilpotent (pCore 2 (planeLocal (F := F))) := pCore_isPGroup.isNilpotent
    infer_instance
  have ht : B' = ⊤ := perfect_normal_eq_top_of_simple_image Plane.quotientMap
    Plane.quotientMap_surjective B' (fun hs => hB (by
      let := hs
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective))
  have hh := congrArg (map (planeLocal (F := F)).subtype) ht
  simpa only [B', map_subgroupOf_eq_of_le hBL, ← MonoidHom.range_eq_map, range_subtype] using hh

end Theory.SpecificGroups.SymplecticFour
