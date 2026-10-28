module

public import Theory.GroupAction.FourGroupCoreAction.Kernel.DihedralRigidity

/-!
# The four-group action kernel

The fixed-core product and the quotient-action construction reduce the kernel
identities in A.1.14(1) to the trivial-center theorem for a finite group generated
by two conjugate subgroups of order two. Applying that theorem to the literal
quotient proves that the kernel is the generated group’s two-core and the
product of the two point kernels. All normality, prime-core bounds, quotient
maps and actions are those of the original `FourGroupCorePair`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.1.14(1), printed p.23.
-/

public section

open Subgroup
namespace FourGroupCorePair
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {v₁ v₂ : G}
variable (h : FourGroupCorePair V v₁ v₂)
include h

/-- The kernel formula follows once the dihedral argument kills the center
of the literal quotient Y/P. Retained as a conditional interface for clients
that already have that center calculation. -/
theorem kernel_formula_of_center_quotient_eq_bot
    (hz : center h.KernelQuotient = ⊥) :
    (generated v₁ v₂).pCoreIn 2 = generated v₁ v₂ ⊓ centralizer (V : Set G) ∧
    generated v₁ v₂ ⊓ centralizer (V : Set G) = kernelJoin V v₁ v₂ ∧
    h.action.ker = pCore 2 (generated v₁ v₂) := by
  have hqker : h.quotientAction.ker = ⊥ :=
    le_bot_iff.mp (h.quotientAction_ker_le_center.trans_eq hz)
  have hi : Function.Injective h.quotientAction :=
    (MonoidHom.ker_eq_bot_iff h.quotientAction).mp hqker
  have heq : generated v₁ v₂ ⊓ centralizer (V : Set G) = kernelJoin V v₁ v₂ := by
    apply le_antisymm
    · intro x hx
      let y : generated v₁ v₂ := ⟨x, hx.1⟩
      have hy : y ∈ h.action.ker := by rw [h.action_ker]; exact hx.2
      have hp : h.kernelProjection y = 1 := by
        apply hi
        rw [h.quotientAction_projection, map_one]
        exact hy
      change y ∈ h.kernelProjection.ker at hp
      rw [h.kernelProjection_ker] at hp
      exact hp
    · exact le_inf kernelJoin_le_generated kernelJoin_le_centralizer
  have hcore : (generated v₁ v₂).pCoreIn 2 =
      generated v₁ v₂ ⊓ centralizer (V : Set G) :=
    le_antisymm h.twoCore_le_generated_inf_centralizer (heq.le.trans h.kernelJoin_le_twoCore)
  refine ⟨hcore, heq, ?_⟩
  apply map_injective (generated v₁ v₂).subtype_injective
  rw [h.action_ker, subgroupOf_map_subtype]
  change centralizer (V : Set G) ⊓ generated v₁ v₂ = (generated v₁ v₂).pCoreIn 2
  rw [hcore, inf_comm]

/-- The action kernel, the embedded two-core, and the fixed-core product in
A.1.14(1), for the original four-group and its two point cores. -/
theorem kernel_formula :
    (generated v₁ v₂).pCoreIn 2 = generated v₁ v₂ ⊓ centralizer (V : Set G) ∧
    generated v₁ v₂ ⊓ centralizer (V : Set G) = kernelJoin V v₁ v₂ ∧
    h.action.ker = pCore 2 (generated v₁ v₂) :=
  h.kernel_formula_of_center_quotient_eq_bot h.kernelQuotient_center_eq_bot

/-- The two-core of the generated group is its centralizer of the four-group. -/
theorem twoCore_eq_generated_inf_centralizer :
    (generated v₁ v₂).pCoreIn 2 = generated v₁ v₂ ⊓ centralizer (V : Set G) :=
  h.kernel_formula.1

/-- The centralizer inside the generated group is the fixed-core product. -/
theorem generated_inf_centralizer_eq_kernelJoin :
    generated v₁ v₂ ⊓ centralizer (V : Set G) = kernelJoin V v₁ v₂ :=
  h.kernel_formula.2.1

/-- The literal action on the four-group has precisely the two-core as kernel. -/
theorem action_ker_eq_twoCore : h.action.ker = pCore 2 (generated v₁ v₂) :=
  h.kernel_formula.2.2

/-- The embedded two-core is the product of the two point kernels. -/
theorem twoCore_eq_kernelJoin : (generated v₁ v₂).pCoreIn 2 = kernelJoin V v₁ v₂ :=
  h.twoCore_eq_generated_inf_centralizer.trans h.generated_inf_centralizer_eq_kernelJoin

/-- Membership in the source two-core means membership in the literal product
of the two point kernels, in their original order. -/
theorem mem_twoCore_iff (x : G) : x ∈ (generated v₁ v₂).pCoreIn 2 ↔
    ∃ a ∈ pointKernel V v₁, ∃ b ∈ pointKernel V v₂, a * b = x := by
  rw [h.twoCore_eq_kernelJoin]
  exact h.mem_kernelJoin_iff x

end FourGroupCorePair
