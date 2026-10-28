module

public import Theory.GroupTheory.PPerfectHom
public import Theory.Representation.BinaryOffender.Basic
/-!
# Fixed vectors through a central kernel for a two-perfect actor

The displacement of a quotient-fixed vector is a homomorphism from the
actor into the additive binary module, because the kernel is fixed
pointwise. Two-perfectness kills that homomorphism. Thus quotient-fixed
vectors lift without asserting a complement or a splitting of the module.
The paired natural Baumann argument uses this on the opposite support.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
theorem fixed_of_pPerfect_central_kernel
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (hA : IsPPerfect 2 A)
    (f : V →ₗ[ZMod 2] W) (hk : f.ker ≤ fixedSpace ρ A)
    (v : V) (hv : ∀ a : A, f (ρ a v) = f v) : v ∈ fixedSpace ρ A := by
  have hdisp (a b : A) : ρ a (ρ b v - v) = ρ b v - v := by
    apply hk
    change f (ρ b v - v) = 0
    rw [map_sub, hv, sub_self]
  let d : A →* Multiplicative V := {
    toFun := fun a => Multiplicative.ofAdd (ρ a v - v)
    map_one' := by simp
    map_mul' := by
      intro a b
      change ρ ((a : G) * b) v - v = (ρ a v - v) + (ρ b v - v)
      rw [map_mul, Module.End.mul_apply]
      have hh := hdisp a b
      rw [map_sub] at hh
      exact sub_eq_iff_eq_add.mp hh ▸ (by abel) }
  have hp : IsPGroup 2 (Multiplicative V) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1) • x.toAdd = 0
    calc
      (2 ^ 1 : ℕ) • x.toAdd = (2 : ZMod 2) • x.toAdd := by
        simpa using (Nat.cast_smul_eq_nsmul (ZMod 2) 2 x.toAdd).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hd := hA.hom_eq_one_of_isPGroup hp d
  intro a
  have hh := congrArg (fun k : A →* Multiplicative V => (k a).toAdd) hd
  change ρ a v - v = 0 at hh
  exact sub_eq_zero.mp hh
end Representation.BinaryOffender
