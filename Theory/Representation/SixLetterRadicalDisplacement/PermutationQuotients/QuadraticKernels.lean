module

public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.QuadraticKernels.FiniteSpan
public import Theory.Representation.BinaryOffender.Defs

/-!
# Quadratic obstructions on noncentral syntheme quotients

Quadratic action kills the corresponding second displacements. Equivariance
makes the kernel invariant, so the finite spanning identities force it to
contain the augmentation core. Surjectivity then makes the quotient action
trivial, contradicting the explicit noncentrality hypothesis. Conjugating the
actors transports quadraticity, giving the exclusion for every conjugate of
the coordinate four-group as well.

These are the permutation-quotient obstructions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 13.8.34, printed p.968
(PDF p.985), using 13.8.4(5),(6). Nonzero dimension alone would not suffice:
the augmentation quotient is a nonzero trivial module.
-/

public section

open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients

private theorem equivariant_kernel_invariant {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (φ : G →* S) (σ : Representation (ZMod 2) G Q) (f : P →ₗ[ZMod 2] Q)
    (heq : ∀ g v, f (rho (φ g) v) = σ g (f v)) :
    ∀ g v, v ∈ f.ker → rho (φ g) v ∈ f.ker := by
  intro g v hv
  change f v = 0 at hv
  change f (rho (φ g) v) = 0
  rw [heq, hv, map_zero]

private theorem equivariant_second_mem_kernel {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (φ : G →* S) (σ : Representation (ZMod 2) G Q) (f : P →ₗ[ZMod 2] Q)
    (heq : ∀ g v, f (rho (φ g) v) = σ g (f v)) (a b : G)
    (h : ∀ v, σ a (σ b v - v) = σ b v - v) (v : P) :
    rho (φ a) (rho (φ b) v - v) - (rho (φ b) v - v) ∈ f.ker := by
  change f (rho (φ a) (rho (φ b) v - v) - (rho (φ b) v - v)) = 0
  rw [map_sub, heq, map_sub, heq, h, sub_self]

/-- The even radical cannot be quadratic on a noncentral equivariant `S₆` quotient. -/
theorem not_quadratic_D0 {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnoncentral : ∃ g v, σ g v ≠ v) : ¬ IsQuadratic σ D0 := by
  intro hq
  have ha : swap01 * swap23 ∈ D0 :=
    ⟨D.mul_mem swap01_mem_D swap23_mem_D, by
      change Equiv.Perm.sign (swap01 * swap23) = 1
      decide⟩
  have hker : P0 ≤ f.ker := core_le_of_alternating_second_displacements f.ker
    (fun g => equivariant_kernel_invariant (MonoidHom.id S) σ f heq g.val)
    (equivariant_second_mem_kernel (MonoidHom.id S) σ f heq _ _
      (hq _ ha _ swap01_swap45_mem_D0))
  obtain ⟨g, v, hv⟩ := hnoncentral
  exact hv (quotient_trivial_of_core_le_ker (MonoidHom.id S) σ f hf heq hker g v)

/-- The coordinate four-group cannot be quadratic on a noncentral `S₆` quotient. -/
theorem not_quadratic_coordinateFour {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnoncentral : ∃ g v, σ g v ≠ v) : ¬ IsQuadratic σ coordinateFour := by
  intro hq
  have hker : P0 ≤ f.ker := core_le_of_symmetric_second_displacements f.ker
    (equivariant_kernel_invariant (MonoidHom.id S) σ f heq)
    (equivariant_second_mem_kernel (MonoidHom.id S) σ f heq _ _
      (hq _ (by decide) _ (by decide)))
  obtain ⟨g, v, hv⟩ := hnoncentral
  exact hv (quotient_trivial_of_core_le_ker (MonoidHom.id S) σ f hf heq hker g v)

/-- The intrinsic alternating radical cannot be quadratic on a noncentral `A₆` quotient. -/
theorem not_quadratic_alternatingRadical {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rhoA g v) = σ g (f v))
    (hnoncentral : ∃ g v, σ g v ≠ v) : ¬ IsQuadratic σ alternatingRadical := by
  intro hq
  let a : alternatingGroup (Fin 6) := ⟨swap01 * swap23, by decide⟩
  let b : alternatingGroup (Fin 6) := ⟨swap01 * swap45, by decide⟩
  have ha : a ∈ alternatingRadical := D.mul_mem swap01_mem_D swap23_mem_D
  have hb : b ∈ alternatingRadical := D.mul_mem swap01_mem_D swap45_mem_D
  have hker : P0 ≤ f.ker := core_le_of_alternating_second_displacements f.ker
    (equivariant_kernel_invariant (alternatingGroup (Fin 6)).subtype σ f heq)
    (equivariant_second_mem_kernel (alternatingGroup (Fin 6)).subtype σ f heq a b
      (hq a ha b hb))
  obtain ⟨g, v, hv⟩ := hnoncentral
  exact hv (quotient_trivial_of_core_le_ker
    (alternatingGroup (Fin 6)).subtype σ f hf heq hker g v)

private theorem quadratic_of_conjugate {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) G Q) (A : Subgroup G) (g : G)
    (hq : IsQuadratic σ (A.map (MulAut.conj g).toMonoidHom)) : IsQuadratic σ A := by
  have hinv (v : Q) : σ g⁻¹ (σ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro a ha b hb v
  have h := hq (g * a * g⁻¹) ⟨a, ha, rfl⟩ (g * b * g⁻¹) ⟨b, hb, rfl⟩ (σ g v)
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv] using congrArg (σ g⁻¹) h

/-- Every symmetric conjugate of the coordinate four-group is excluded. -/
theorem not_quadratic_coordinateFour_conjugate {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnoncentral : ∃ g v, σ g v ≠ v) (g : S) :
    ¬ IsQuadratic σ (coordinateFour.map (MulAut.conj g).toMonoidHom) := by
  intro hq
  exact not_quadratic_coordinateFour σ f hf heq hnoncentral
    (quadratic_of_conjugate σ coordinateFour g hq)

end Representation.SixLetterRadicalDisplacement.PermutationQuotients
