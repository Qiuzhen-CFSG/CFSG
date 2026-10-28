module
public import Theory.Representation.BinaryPermutation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Permutation embeddings from separating binary functionals

A linear functional fixed by a subgroup D gives an equivariant map into
functions on the left cosets of D. Its conjugates separate vectors exactly
when that map is injective. Evaluation uses inverse representatives, matching
the left permutation action.

The original centralizer quotient in Aschbacher--Smith 13.8.33, printed p.968,
uses this construction with the functional defined by an index-two seed
centralizer and the original point parabolic as D.
-/

public section
namespace Representation.BinaryCosetFunctional
open Subgroup
variable {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]

/-- The functional transported along a left coset. -/
@[expose] noncomputable def orbit (ρ : Representation (ZMod 2) A X) (D : Subgroup A)
    (f : X →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a ∈ D, ∀ x, f (ρ a x) = f x) : A ⧸ D → (X →ₗ[ZMod 2] ZMod 2) :=
  fun c => Quotient.liftOn' c (fun a => f.comp (ρ a⁻¹)) (by
    intro a b hab
    apply LinearMap.ext
    intro x
    have he := hf (b⁻¹ * a) (by simpa only [mul_inv_rev, inv_inv] using D.inv_mem (QuotientGroup.leftRel_apply.mp hab)) (ρ a⁻¹ x)
    simpa only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
      mul_assoc, mul_inv_cancel, mul_one] using he.symm)

/-- Evaluate the transported functionals on the original vector. -/
@[expose] noncomputable def embedding (ρ : Representation (ZMod 2) A X) (D : Subgroup A)
    [Fintype (A ⧸ D)] (f : X →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a ∈ D, ∀ x, f (ρ a x) = f x) :
    ρ.IntertwiningMap ((BinaryPermutation.representation (A ⧸ D)).comp
      (MulAction.toPermHom A (A ⧸ D))) where
  toLinearMap := LinearMap.pi (orbit ρ D f hf)
  isIntertwining' := by
    intro a
    apply LinearMap.ext
    intro x
    funext c
    induction c using QuotientGroup.induction_on with
    | H b =>
      change f (ρ b⁻¹ (ρ a x)) = f (ρ (a⁻¹ * b)⁻¹ x)
      rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

@[simp] theorem embedding_mk (ρ : Representation (ZMod 2) A X) (D : Subgroup A)
    [Fintype (A ⧸ D)] (f : X →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a ∈ D, ∀ x, f (ρ a x) = f x) (x : X) (a : A) :
    embedding ρ D f hf x (QuotientGroup.mk a) = f (ρ a⁻¹ x) := rfl

/-- Separation by the orbit of the functional gives injectivity. -/
theorem embedding_injective (ρ : Representation (ZMod 2) A X) (D : Subgroup A)
    [Fintype (A ⧸ D)] (f : X →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a ∈ D, ∀ x, f (ρ a x) = f x)
    (hsep : ∀ x, (∀ a, f (ρ a x) = 0) → x = 0) :
    Function.Injective (embedding ρ D f hf) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro x hx
  apply hsep x
  intro a
  have he := congrFun hx (QuotientGroup.mk a⁻¹)
  change embedding ρ D f hf x (QuotientGroup.mk a⁻¹) = 0 at he
  simpa only [embedding_mk, inv_inv] using he

/-- Reindex the injection by a specified equivariant coset identification. -/
theorem exists_reindexed_embedding {Ω : Type*} [Fintype Ω]
    (ρ : Representation (ZMod 2) A X) (D : Subgroup A)
    [Fintype (A ⧸ D)] (f : X →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a ∈ D, ∀ x, f (ρ a x) = f x)
    (hsep : ∀ x, (∀ a, f (ρ a x) = 0) → x = 0)
    (π : A →* Equiv.Perm Ω) (E : (A ⧸ D) ≃ Ω)
    (hE : ∀ a c, E (a • c) = π a (E c)) :
    ∃ j : ρ.IntertwiningMap ((BinaryPermutation.representation Ω).comp π),
      Function.Injective j := by
  let b := embedding ρ D f hf
  let r := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) E.symm
  let j := r.toLinearMap.comp b.toLinearMap
  have hj : ∀ a x, j (ρ a x) = BinaryPermutation.representation Ω (π a) (j x) := by
    intro a x
    funext i
    change b (ρ a x) (E.symm i) = b x (E.symm ((π a).symm i))
    rw [b.isIntertwining]
    change b x (a⁻¹ • E.symm i) = _
    apply congrArg (b x)
    apply E.injective
    rw [hE,E.apply_symm_apply,E.apply_symm_apply,map_inv]
    rfl
  exact ⟨j.intertwiningMap_of_isIntertwiningMap _ _ hj,
    r.injective.comp (embedding_injective ρ D f hf hsep)⟩

end Representation.BinaryCosetFunctional
