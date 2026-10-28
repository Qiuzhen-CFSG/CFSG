module

public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Automorphism actions through a solvable kernel

A surjection with solvable kernel identifies the source and target radical
quotients. For equivariant automorphism actions, faithfulness on the source
radical quotient therefore implies faithfulness on the target radical
quotient. The proof uses the actual surjection and quotient projections.

This supplies transport from L to its literal two-core quotient in the
terminal four-group obstruction of Aschbacher--Smith §13.1, p.876.
-/

public section
open Subgroup
namespace Subgroup
variable {G H E : Type*} [Group G] [Finite G] [Group H] [Finite H] [Group E]

/-- Equivariant descent through a solvable kernel preserves faithfulness
on radical quotients. -/
theorem radical_quotient_action_injective_of_solvable_kernel
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (ρ : E →* MulAut G) (σ : E →* MulAut H)
    (he : ∀ a x, σ a (f x) = f (ρ a x))
    (hi : Function.Injective ((quotientAut (solvableRadical G)).comp ρ)) :
    Function.Injective ((quotientAut (solvableRadical H)).comp σ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (((quotientAut (solvableRadical H)).comp σ).ker).eq_bot_iff_forall.mpr
  intro a ha
  apply hi
  rw [map_one]
  apply MulEquiv.ext
  intro x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (solvableRadical G) x
  change quotientAut (solvableRadical G) (ρ a)
    (QuotientGroup.mk' (solvableRadical G) x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [← comap_solvableRadical_eq_of_solvable_ker f hf]
  change f (x⁻¹ * ρ a x) ∈ solvableRadical H
  rw [map_mul, map_inv, ← he]
  apply QuotientGroup.eq.mp
  have hh := DFunLike.congr_fun (MonoidHom.mem_ker.mp ha)
    (QuotientGroup.mk' (solvableRadical H) (f x))
  change quotientAut (solvableRadical H) (σ a)
    (QuotientGroup.mk' (solvableRadical H) (f x)) = _ at hh
  rw [quotientAut_apply_mk] at hh
  exact hh.symm

end Subgroup
