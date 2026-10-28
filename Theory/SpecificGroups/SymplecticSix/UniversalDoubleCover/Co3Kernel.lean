module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Witness
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel.Checks

/-!
# The kernel of the concrete Co₃ symplectic projection

A checked two-graph on the 276 letters is invariant under the three numerator
words. A kernel element fixes the 36 letters used in the quotient, so preserves
the graph with isolated vertex 4. The adjacency signatures of the letters have
exactly the fibers {x, z x}. A checked two-step connection then forces a kernel
element fixing letter 0 to fix every letter. Multiplication by z reduces every
kernel element to that case. Thus the kernel is precisely ⟨z⟩ and is central.

This proves the missing kernel assertion for the concrete 2Sp₆(2) witness
motivated by GLS3 Table 5.3j and Aschbacher–Smith A.2.19, pp.40–41. No ambient
Co₃ order, simplicity, centralizer classification or numerator perfectness is
used. See `Co3Kernel/source/README.md` for certificate provenance.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
open Sporadic.LeechRelated.Co3
open Sporadic.LeechRelated.Co3.CentralizerSection
open Co3Kernel

private theorem xor_cancel_six (a b c u v w : Bool) :
    (((a ^^ u) ^^ v) ^^ ((b ^^ u) ^^ w) ^^ ((c ^^ v) ^^ w)) =
      ((a ^^ b) ^^ c) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases w <;> rfl

private def triangleGroup : Subgroup (Equiv.Perm (Fin 276)) where
  carrier := {p | ∀ x y t, triangle (p x) (p y) (p t) = triangle x y t}
  one_mem' := by intro x y t; rfl
  mul_mem' := by
    intro p q hp hq x y t
    exact (hp (q x) (q y) (q t)).trans (hq x y t)
  inv_mem' := by
    intro p hp x y t
    have h := hp (p⁻¹ x) (p⁻¹ y) (p⁻¹ t)
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

private theorem generator_preserves (i : Fin 3) : Tables.generatorTable i ∈ triangleGroup := by
  intro x y t
  unfold triangle
  rw [generator_switch i x y, generator_switch i x t, generator_switch i y t]
  exact xor_cancel_six _ _ _ _ _ _

private theorem preserves_triangle (g : Co3Witness.ExtensionGroup) (x y t : Fin 276) :
    triangle (inclusion g.val x) (inclusion g.val y) (inclusion g.val t) = triangle x y t := by
  have hle : numerator ≤ triangleGroup.comap inclusion := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change inclusion (generator i) ∈ triangleGroup
    rw [inclusion_generator]
    exact generator_preserves i
  exact hle g.property x y t

namespace Co3Witness

private theorem fixes_fixed_of_kernel (g : ExtensionGroup) (hg : g ∈ matrixProjection.ker)
    (i : Fin 36) : inclusion g.val (Tables.fixedPoint i) = Tables.fixedPoint i := by
  rw [matrixProjection_ker] at hg
  have hp : pointAction g = 1 := congrArg Subtype.val (show pointQuotient g = 1 from hg)
  rw [← pointAction_agrees, hp]
  rfl

private theorem adjacent_of_kernel (g : ExtensionGroup) (hg : g ∈ matrixProjection.ker)
    (x y : Fin 276) : adjacent (inclusion g.val x) (inclusion g.val y) = adjacent x y := by
  have ha : inclusion g.val 4 = 4 := fixes_fixed_of_kernel g hg 0
  have ht := preserves_triangle g 4 x y
  rw [ha, triangle_anchor, triangle_anchor] at ht
  exact ht

private theorem pair_of_kernel (g : ExtensionGroup) (hg : g ∈ matrixProjection.ker)
    (x : Fin 276) : inclusion g.val x = x ∨ inclusion g.val x = Tables.tableZ x := by
  have hs : signature (inclusion g.val x) = signature x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [signature_spec _ ⟨i, hi⟩, signature_spec _ ⟨i, hi⟩]
    have he := adjacent_of_kernel g hg (Tables.fixedPoint ⟨i, hi⟩) x
    rw [fixes_fixed_of_kernel g hg] at he
    exact he
  exact signature_fibers x (inclusion g.val x) hs.symm

private theorem eq_one_of_kernel_fixes_zero (g : ExtensionGroup)
    (hg : g ∈ matrixProjection.ker) (hzero : inclusion g.val 0 = 0) : g = 1 := by
  apply Subtype.ext
  apply inclusion_injective
  apply Equiv.ext
  intro x
  change inclusion g.val x = x
  rcases pair_of_kernel g hg x with hx | hx
  · exact hx
  by_cases hz : Tables.tableZ x = x
  · exact hx.trans hz
  have hb := bridge_separates x hz
  have hw : inclusion g.val (bridge x) = bridge x := by
    rcases pair_of_kernel g hg (bridge x) with hw | hw
    · exact hw
    have he := adjacent_of_kernel g hg 0 (bridge x)
    rw [hzero, hw] at he
    exact False.elim (hb.1 he.symm)
  have he := adjacent_of_kernel g hg (bridge x) x
  rw [hw, hx] at he
  exact False.elim (hb.2 he.symm)

/-- The actual fixed-point restriction kernel has just its two expected elements. -/
theorem matrixProjection_kernel_cases (g : ExtensionGroup) (hg : g ∈ matrixProjection.ker) :
    g = 1 ∨ g = z := by
  rcases pair_of_kernel g hg 0 with hzero | hzero
  · exact Or.inl (eq_one_of_kernel_fixes_zero g hg hzero)
  right
  have hk : z⁻¹ * g ∈ matrixProjection.ker :=
    matrixProjection.ker.mul_mem (matrixProjection.ker.inv_mem z_mem_kernel) hg
  have hfix : inclusion (z⁻¹ * g).val 0 = 0 := by
    change inclusion (z.val⁻¹ * g.val) 0 = 0
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, hzero, z_val, inclusion_involution]
    exact Equiv.symm_apply_apply _ _
  have he := eq_one_of_kernel_fixes_zero (z⁻¹ * g) hk hfix
  exact (inv_mul_eq_one.mp he).symm

/-- The literal projection to Sp₆(2) has kernel generated by the marked involution. -/
theorem matrixProjection_ker_eq_zpowers : matrixProjection.ker = Subgroup.zpowers z := by
  apply le_antisymm
  · intro g hg
    rcases matrixProjection_kernel_cases g hg with rfl | rfl
    · exact (Subgroup.zpowers z).one_mem
    · exact Subgroup.mem_zpowers z
  · exact Subgroup.zpowers_le_of_mem z_mem_kernel

/-- The missing central-extension obligation for the concrete Co₃ witness. -/
theorem matrixProjection_ker_le_center : matrixProjection.ker ≤ Subgroup.center ExtensionGroup := by
  rw [matrixProjection_ker_eq_zpowers]
  exact Subgroup.zpowers_le_of_mem z_mem_center

end Co3Witness
end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
