module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
import Mathlib.Tactic.Group
/-!
# The actual max1 group and its relative automorphism displacement

The carriers are the literal ATLAS max1 subgroup and its certified elementary
normal closure, at the canonical generator identities. The existing faithful
quotient action identifies the centralizer of the kernel with the kernel.
Consequently an automorphism fixing the kernel pointwise induces the identity
on the quotient. Its displacement is the right cocycle
`delta(gh) = h⁻¹ * delta(g) * h * delta(h)`.

The bounded masks give a bijection with the actual kernel. Equality of
local automorphisms is detected by the two actual ATLAS generators.
These interfaces support the finite relative-rigidity argument, without any
assumption that local or global automorphisms are inner.

Source: literal ATLAS `J4G1-max1W1`, as documented in `Cardinality.Subgroup`;
local structure motivation: GLS3, Table 5.3i.
-/

@[expose] public section
namespace Janko4.Max1RelativeRigidity
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
abbrev M := max1Subgroup matrixA_mul_self matrixB_pow_four
abbrev K : Subgroup M := localKernel matrixA_mul_self matrixB_pow_four
abbrev x : M := localX matrixA_mul_self matrixB_pow_four
abbrev y : M := localY matrixA_mul_self matrixB_pow_four
abbrev v : M := kernelPair matrixA_mul_self matrixB_pow_four
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

/-- Bounded masks remain distinct in the actual kernel. -/
theorem maskValue_injective : Function.Injective
    (fun m : Fin 2048 => maskValue matrixA_mul_self matrixB_pow_four m.val) := by
  intro m n h
  have he := coordinates_injective matrixA_mul_self matrixB_pow_four h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · exact congrFun he ⟨i, hi⟩
  · have hp : 2 ^ 11 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le n.isLt hp)]

/-- The actual kernel, with exactly its 2048 binary masks. -/
noncomputable def maskEquiv : Fin 2048 ≃ K :=
  Equiv.ofBijective _ ⟨maskValue_injective,
    maskValue_surjective matrixA_mul_self matrixB_pow_four⟩

@[simp] theorem maskEquiv_apply (m : Fin 2048) :
    maskEquiv m = maskValue matrixA_mul_self matrixB_pow_four m.val := rfl

/-- Fixing the kernel forces every right displacement into that kernel. -/
theorem displacement_mem (phi : MulAut M)
    (hfix : ∀ e : K, phi e = e) (g : M) : g⁻¹ * phi g ∈ K := by
  change g⁻¹ * phi g ∈ localKernel matrixA_mul_self matrixB_pow_four
  rw [← LocalStructure.centralizer_localKernel matrixA_mul_self matrixB_pow_four]
  intro e he
  have h := hfix ⟨g * e * g⁻¹, Subgroup.Normal.conj_mem inferInstance e he g⟩
  simp only [map_mul, map_inv, hfix ⟨e, he⟩] at h
  have hh := congrArg (fun t : M => g⁻¹ * t * phi g) h
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- Pointwise kernel fixation forces identity on the actual quotient. -/
theorem quotient_fixed (phi : MulAut M)
    (hfix : ∀ e : K, phi e = e) (g : M) :
    QuotientGroup.mk' K (phi g) = QuotientGroup.mk' K g := by
  have h := (QuotientGroup.eq_one_iff (g⁻¹ * phi g)).mpr (displacement_mem phi hfix g)
  change QuotientGroup.mk' K (g⁻¹ * phi g) = 1 at h
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

/-- Right displacement; its conjugation convention is recorded in `delta_mul`. -/
def delta (phi : MulAut M) (g : M) : M := g⁻¹ * phi g

/-- The right cocycle identity, valid before assuming kernel fixation. -/
theorem delta_mul (phi : MulAut M) (g h : M) :
    delta phi (g * h) = h⁻¹ * delta phi g * h * delta phi h := by
  simp only [delta, map_mul, mul_inv_rev]
  group

/-- The two literal ATLAS generators detect equality of local automorphisms. -/
theorem aut_ext (phi psi : MulAut M) (hx : phi x = psi x) (hy : phi y = psi y) :
    phi = psi := by
  have h : phi.toMonoidHom = psi.toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense (localXY_generate matrixA_mul_self matrixB_pow_four)
      (by intro g hg; rcases hg with rfl | hg
          · exact hx
          · obtain rfl := Set.mem_singleton_iff.mp hg; exact hy)
  exact MulEquiv.ext (fun g => DFunLike.congr_fun h g)
end Janko4.Max1RelativeRigidity
