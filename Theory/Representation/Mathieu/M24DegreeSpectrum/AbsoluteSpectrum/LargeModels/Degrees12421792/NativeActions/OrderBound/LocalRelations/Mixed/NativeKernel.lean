module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.Contracts

/-!
# The cyclic kernel in the marked native image

The six words vanish in the native permutation image. This only proves their
vanishing in the source group after the cyclic trace and its separate order-23
premise are supplied. The native map is used solely on that cyclic subgroup;
no ambient finiteness or injectivity is assumed.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed
open Subgroup.CosetWordCertificate Sporadic.Mathieu

def firstPermutation : Equiv.Perm (Fin 24) where
  toFun := ![20, 4, 7, 17, 1, 13, 9, 2, 15, 6, 19, 18, 21, 5, 16, 8, 14, 3, 11, 10, 0, 12, 23, 22]
  invFun := ![20, 4, 7, 17, 1, 13, 9, 2, 15, 6, 19, 18, 21, 5, 16, 8, 14, 3, 11, 10, 0, 12, 23, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def secondPermutation : Equiv.Perm (Fin 24) where
  toFun := ![21, 16, 4, 18, 22, 7, 10, 8, 11, 1, 3, 5, 0, 9, 17, 14, 13, 20, 6, 2, 15, 23, 19, 12]
  invFun := ![12, 9, 19, 10, 2, 11, 18, 5, 7, 13, 6, 8, 23, 16, 15, 20, 1, 14, 3, 22, 17, 0, 4, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def imageGenerator : Fin 2 → Equiv.Perm (Fin 24) :=
  ![firstPermutation, secondPermutation]

set_option maxRecDepth 10000 in
private theorem imageGenerator_exact : ∀ s : Fin 2,
    imageGenerator s = subgroupWord m24GeneratorA m24GeneratorB s := by decide +kernel

noncomputable def nativeMap : UniversalGroup →* Equiv.Perm (Fin 24) :=
  M24.subtype.comp toCarrier

theorem nativeMap_boundGenerator (s : Fin 2) :
    nativeMap (boundGenerator s) = imageGenerator s := by
  rw [boundGenerator, map_subgroupWord]
  simpa [nativeMap, generator, a, b] using (imageGenerator_exact s).symm

private theorem map_eval {G K α : Type*} [Group G] [Group K]
    (f : G →* K) (g : α → G) (w : Word α) :
    f (eval g w) = eval (fun s => f (g s)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [eval_cons, map_mul, ih]
    split <;> simp [map_inv]

theorem nativeMap_eval (w : Word (Fin 2)) :
    nativeMap (eval boundGenerator w) = eval imageGenerator w := by
  rw [map_eval]
  simp only [nativeMap_boundGenerator]

private theorem image_mixed : ∀ i : Fin 6,
    eval imageGenerator (localRelatorLetters ⟨i.val + 3, by omega⟩) = 1 := by
  decide +kernel

theorem nativeMap_mixed (i : Fin 6) :
    nativeMap (eval boundGenerator (localRelatorLetters ⟨i.val + 3, by omega⟩)) = 1 := by
  rw [nativeMap_eval, image_mixed]

private theorem image_cycle_ne_one : eval imageGenerator cycleLetters ≠ 1 := by
  decide +kernel

/-- The order-23 premise makes the native map faithful on the one cyclic subgroup
used by the trace. It does not assert faithfulness on the ambient group. -/
theorem eq_one_of_cycle_mem (hp : CyclePowerRelation) {v : UniversalGroup}
    (hv : v ∈ Subgroup.zpowers cycleElement) (hm : nativeMap v = 1) : v = 1 := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have hn : nativeMap cycleElement ≠ 1 := by
    simpa only [cycleElement, nativeMap_eval] using image_cycle_ne_one
  have ho : orderOf (nativeMap cycleElement) = 23 :=
    orderOf_eq_prime (by rw [← map_pow, hp, map_one]) hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hd : (23 : ℤ) ∣ k := by
    have hz : (orderOf (nativeMap cycleElement) : ℤ) ∣ k :=
      orderOf_dvd_iff_zpow_eq_one.mpr (by simpa only [map_zpow] using hm)
    simpa [ho] using hz
  obtain ⟨j, rfl⟩ := hd
  rw [zpow_mul, zpow_ofNat, hp, one_zpow]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Mixed
