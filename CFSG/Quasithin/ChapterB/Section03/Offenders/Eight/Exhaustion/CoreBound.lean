module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace

/-!
# Augmentation and the core offender bound

The kernel of augmentation on the full fixed space is the core fixed space.
Rank-nullity bounds their dimension difference by one. If the group has a
common fixed coordinate, its coordinate vector makes augmentation surjective,
so the full and core fixed codimensions agree.

These are the linear-algebra reductions for the degree-eight necessity proof
of Aschbacher–Smith, Proposition B.3.2(5), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open BinaryPermutation Representation.BinaryOffender

private noncomputable def fixedAugmentation (A : Subgroup (Equiv.Perm (Fin 8))) :=
  (augmentation (Fin 8)).domRestrict (fixedSpace (representation (Fin 8)) A)

private noncomputable def fixedAugmentationKerEquiv
    (A : Subgroup (Equiv.Perm (Fin 8))) :
    LinearMap.ker (fixedAugmentation A) ≃ₗ[ZMod 2]
      fixedSpace (coreRepresentation (Fin 8)) A :=
  { toFun := fun v => ⟨⟨v.val.val, v.property⟩,
      (mem_core_fixedSpace_iff A _).mpr
        ((mem_full_fixedSpace_iff A _).mp v.val.property)⟩
    invFun := fun v => ⟨⟨v.val.val,
      (mem_full_fixedSpace_iff A _).mpr
        ((mem_core_fixedSpace_iff A _).mp v.property)⟩, v.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Passing to the core changes the dimension of fixed vectors by at most one. -/
theorem finrank_fixedSpace_core_bounds (A : Subgroup (Equiv.Perm (Fin 8))) :
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 8)) A) ≤
        Module.finrank (ZMod 2) (fixedSpace (representation (Fin 8)) A) ∧
      Module.finrank (ZMod 2) (fixedSpace (representation (Fin 8)) A) ≤
        Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 8)) A) + 1 := by
  have h := (fixedAugmentation A).finrank_range_add_finrank_ker
  rw [(fixedAugmentationKerEquiv A).finrank_eq] at h
  have hr := Submodule.finrank_le (LinearMap.range (fixedAugmentation A))
  rw [Module.finrank_self] at hr
  exact ⟨by omega, by omega⟩

/-- The core fixed codimension is either the full one or one less. -/
theorem fixedCodim_core_bounds (A : Subgroup (Equiv.Perm (Fin 8))) :
    fixedCodim (coreRepresentation (Fin 8)) A ≤ fixedCodim (representation (Fin 8)) A ∧
      fixedCodim (representation (Fin 8)) A ≤
        fixedCodim (coreRepresentation (Fin 8)) A + 1 := by
  have h := finrank_fixedSpace_core_bounds A
  have hF := fixedCodim_add_finrank (representation (Fin 8)) A
  have hC := fixedCodim_add_finrank (coreRepresentation (Fin 8)) A
  rw [finrank_full] at hF
  rw [finrank_core] at hC
  simp only [Fintype.card_fin] at hF hC
  omega

/-- A common fixed coordinate makes augmentation on the fixed space surjective. -/
theorem fixedCodim_core_eq_full_of_fixed_point
    {A : Subgroup (Equiv.Perm (Fin 8))} {x : Fin 8}
    (hx : ∀ a ∈ A, a x = x) :
    fixedCodim (coreRepresentation (Fin 8)) A =
      fixedCodim (representation (Fin 8)) A := by
  classical
  have hs : Function.Surjective (fixedAugmentation A) := by
    intro c
    refine ⟨⟨Pi.single x c, ?_⟩, ?_⟩
    · rw [mem_full_fixedSpace_iff]
      intro a ha i
      have he : a.symm i = x ↔ i = x := by
        rw [a.symm_apply_eq, hx a ha]
      simp only [Pi.single_apply, he]
    · simp [fixedAugmentation, augmentation]
  have h := (fixedAugmentation A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    (fixedAugmentationKerEquiv A).finrank_eq] at h
  have hF := fixedCodim_add_finrank (representation (Fin 8)) A
  have hC := fixedCodim_add_finrank (coreRepresentation (Fin 8)) A
  rw [finrank_full] at hF
  rw [finrank_core] at hC
  simp only [Fintype.card_fin] at hF hC
  omega

/-- A core offender has defect at most one in the full-module orbit bound. -/
theorem full_fixedCodim_le_rank_add_one_of_isOffender_core
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (coreRepresentation (Fin 8)) A) :
    fixedCodim (representation (Fin 8)) A ≤ rank A + 1 :=
  (fixedCodim_core_bounds A).2.trans (Nat.add_le_add_right hA.2 1)

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
