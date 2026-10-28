module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Theory.PGroupCore
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Two-cores and residuals of symplectic determinant kernels

A field of characteristic two has no nonidentity unit of two-power order.
Consequently the two-core of each subspace stabilizer lies in its determinant
kernel. Characteristic-normal transitivity then identifies the intrinsic
cores after embedding them into the same symplectic group.

The determinant character kills the derived group, so the embedded solvable
residual lies in the determinant kernel. The converse follows if the kernel
is perfect. That perfectness hypothesis is explicit: the nonbinary local
matrix calculations, and the natural conjugation-module identifications, are
not asserted by this module.

Source: Aschbacher--Smith, F.1.12(I)(2) and the residual and core assertions
on printed p.264 of the combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

private theorem character_core_le_ker [CharP F 2] {G : Type*} [Group G]
    (f : G →* Fˣ) : pCore 2 G ≤ f.ker := by
  intro g hg
  obtain ⟨k, hk⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨g, hg⟩ : pCore 2 G)
  have h : (f g : F) ^ 2 ^ k = 1 := by
    have hv : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    simpa using congrArg (fun x : G => (f x : F)) hv
  apply Units.ext
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def] using h)

private theorem map_core_eq_of_normal {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (h : pCore 2 G ≤ K) :
    (pCore 2 K).map K.subtype = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map K.subtype⟩
  · have hr : (pCore 2 G).subgroupOf K ≤ pCore 2 K :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective K.subtype
        K.subtype_injective⟩
    simpa only [Subgroup.map_subgroupOf_eq_of_le h] using
      Subgroup.map_mono (f := K.subtype) hr

/-- The parabolic two-core is killed by its determinant character. -/
theorem determinantCharacter_core_le_ker [CharP F 2]
    (W : Submodule F (Vector F)) :
    pCore 2 (stabilizer W) ≤ (determinantCharacter W).ker :=
  character_core_le_ker _

/-- Equality of intrinsic two-cores after mapping to the common ambient group. -/
theorem determinantKernel_core_map [CharP F 2] (W : Submodule F (Vector F)) :
    (pCore 2 (determinantKernel W)).map (determinantKernel W).subtype =
      (pCore 2 (stabilizer W)).map (stabilizer W).subtype := by
  let K := (determinantKernel W).subgroupOf (stabilizer W)
  have h : pCore 2 (stabilizer W) ≤ K := by
    dsimp [K]
    rw [determinantKernel_subgroupOf]
    exact determinantCharacter_core_le_ker W
  let e := Subgroup.subgroupOfEquivOfLe (determinantKernel_le W)
  have he : (determinantKernel W).subtype.comp e.toMonoidHom =
      (stabilizer W).subtype.comp K.subtype := rfl
  rw [← pCore_map_iso 2 e, Subgroup.map_map, he, ← Subgroup.map_map,
    map_core_eq_of_normal K h]

/-- The determinant quotient is abelian, so its kernel contains the residual. -/
theorem determinantKernel_solvableResidual_le (W : Submodule F (Vector F)) :
    (Subgroup.solvableResidual (stabilizer W)).map (stabilizer W).subtype ≤
      determinantKernel W := by
  apply Subgroup.map_mono
  exact (Subgroup.solvableResidual_le_derivedSeries 1).trans
    ((derivedSeries_one _).le.trans (Abelianization.commutator_subset_ker _))

/-- A perfect determinant kernel is exactly the embedded solvable residual. -/
theorem determinantKernel_solvableResidual_eq_of_perfect
    (W : Submodule F (Vector F)) [Group.IsPerfect (determinantKernel W)] :
    (Subgroup.solvableResidual (stabilizer W)).map (stabilizer W).subtype =
      determinantKernel W := by
  exact le_antisymm (determinantKernel_solvableResidual_le W)
    (Subgroup.le_map_solvableResidual_of_isPerfect _ _ (determinantKernel_le W))

/-- The residual identity inside the stabilizer, retaining relative normality. -/
theorem determinantKernel_solvableResidual_relative_of_perfect
    (W : Submodule F (Vector F)) [Group.IsPerfect (determinantKernel W)] :
    Subgroup.solvableResidual (stabilizer W) =
      (determinantKernel W).subgroupOf (stabilizer W) := by
  apply Subgroup.map_injective (stabilizer W).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (determinantKernel_le W)]
  exact determinantKernel_solvableResidual_eq_of_perfect W

/-- The point parabolic and its local factor have the same ambient two-core. -/
theorem pointLocal_core_map [CharP F 2] :
    (pCore 2 (pointLocal (F := F))).map pointLocal.subtype =
      (pCore 2 (pointParabolic (F := F))).map pointParabolic.subtype :=
  determinantKernel_core_map (point F)

/-- The plane parabolic and its local factor have the same ambient two-core. -/
theorem planeLocal_core_map [CharP F 2] :
    (pCore 2 (planeLocal (F := F))).map planeLocal.subtype =
      (pCore 2 (planeParabolic (F := F))).map planeParabolic.subtype :=
  determinantKernel_core_map (plane F)

/-- The point parabolic residual always lies in the chosen local factor. -/
theorem pointParabolic_solvableResidual_le :
    (Subgroup.solvableResidual (pointParabolic (F := F))).map pointParabolic.subtype ≤
      pointLocal :=
  determinantKernel_solvableResidual_le (point F)

/-- The plane parabolic residual always lies in the chosen local factor. -/
theorem planeParabolic_solvableResidual_le :
    (Subgroup.solvableResidual (planeParabolic (F := F))).map planeParabolic.subtype ≤
      planeLocal :=
  determinantKernel_solvableResidual_le (plane F)

/-- Point-parabolic residual identification, conditional on the local perfectness proof. -/
theorem pointParabolic_solvableResidual_eq_of_perfect
    [Group.IsPerfect (pointLocal (F := F))] :
    (Subgroup.solvableResidual (pointParabolic (F := F))).map pointParabolic.subtype =
      pointLocal := by
  let : Group.IsPerfect (determinantKernel (point F)) :=
    ‹Group.IsPerfect (pointLocal (F := F))›
  exact determinantKernel_solvableResidual_eq_of_perfect (point F)

/-- Plane-parabolic residual identification, conditional on the local perfectness proof. -/
theorem planeParabolic_solvableResidual_eq_of_perfect
    [Group.IsPerfect (planeLocal (F := F))] :
    (Subgroup.solvableResidual (planeParabolic (F := F))).map planeParabolic.subtype =
      planeLocal := by
  let : Group.IsPerfect (determinantKernel (plane F)) :=
    ‹Group.IsPerfect (planeLocal (F := F))›
  exact determinantKernel_solvableResidual_eq_of_perfect (plane F)

end Theory.SpecificGroups.SymplecticFour
