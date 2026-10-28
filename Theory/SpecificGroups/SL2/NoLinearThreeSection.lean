module
public import Theory.SpecificGroups.SL2.NoLinearThreeEmbedding
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Binary linear-three sections cannot survive in binary SL₂

The preimage of the concrete upper unitriangular group under the actual
PSL₃(2) quotient is a two-group. Every two-subgroup of binary SL₂ has
exponent two, whereas the unitriangular image contains an element of order
four. A map with kernel contained in the original two-core is impossible.
For a perfect group with simple two-core quotient, every solvable kernel
has that containment. The original cover is retained throughout.

Source: the classical local obstruction used in Aschbacher–Smith,
Lemma 12.3.3, printed p.808; the UT₃ calculation and binary SL₂ Sylow geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open Matrix.PSL3Even.UnipotentGeometry
variable {B F : Type*} [Group B] [Finite B] [Field F] [Finite F] [CharP F 2]

omit [Finite B] in
theorem no_binaryLinearTwo_of_linearThree_twoCore
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* SL(2,F)) (hk : f.ker ≤ pCore 2 B) : False := by
  let a := e.trans Matrix.PSL3Two.equiv.symm
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 B := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  have hu : IsPGroup 2 (U (ZMod 2)) := by
    intro x
    refine ⟨2,?_⟩
    have hx : (x ^ 2) ^ 2 = 1 := (square_eq_one_iff (ZMod 2) _).mpr
      (Or.inl (by simp [pow_two,CharTwo.add_self_eq_zero]))
    simpa only [←pow_mul,show 2 * 2 = 2^2 from rfl] using hx
  let P := (specialLinear (ZMod 2)).range.comap q
  have hp : IsPGroup 2 P :=
    (hu.of_surjective _ (specialLinear (ZMod 2)).rangeRestrict_surjective).comap_of_ker_isPGroup
      q (hqk.symm ▸ pCore_isPGroup)
  let x : U (ZMod 2) := ⟨1,1,0⟩
  obtain ⟨b,hb⟩ := hq (specialLinear (ZMod 2) x)
  have hbP : b ∈ P := by
    change q b ∈ (specialLinear (ZMod 2)).range
    exact hb.symm ▸ ⟨x,rfl⟩
  have hsq := twoSubgroup_pow_two (P.map f) (hp.map f)
    ⟨f b,mem_map_of_mem f hbP⟩
  have hfb : f (b^2) = 1 := by
    rw [map_pow]
    exact congrArg (P.map f).subtype hsq
  have hqb : q (b^2) = 1 := by
    apply a.map_eq_one_iff.mpr
    exact (QuotientGroup.eq_one_iff _).mpr (hk hfb)
  have hx : x^2 = 1 := (specialLinear_injective (ZMod 2)) (by
    rw [map_pow,hb] at hqb
    simpa only [map_pow,map_one] using hqb)
  have hx' := (square_eq_one_iff (ZMod 2) x).mp hx
  simp [x] at hx'

theorem no_binaryLinearTwo_of_solvable_kernel [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* SL(2,F)) [Group.IsSolvable f.ker] : False := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  exact no_binaryLinearTwo_of_linearThree_twoCore e f
    (PerfectCoreTwoExtension.solvable_ker_le_core f)
end Matrix.SpecialLinearGroup

namespace Matrix.PSL3Two
variable {B D F : Type*} [Group B] [Finite B] [Group.IsPerfect B] [Group D]
  [Field F] [Finite F] [CharP F 2]

/-- Solvable local kernels preserve the same obstruction through a second map. -/
theorem no_solvable_kernel_rankOne_local
    (e : (B ⧸ pCore 2 B) ≃* PSL)
    (f : B →* D) [Group.IsSolvable f.ker]
    (r : D →* SL(2,F)) [Group.IsSolvable r.ker] : False := by
  let : Group.IsSolvable (r.comp f).ker := by
    rw [←MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker f r.ker
  exact SpecialLinearGroup.no_binaryLinearTwo_of_solvable_kernel e (r.comp f)
end Matrix.PSL3Two
