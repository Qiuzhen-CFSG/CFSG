module
public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Regular coordinates from a one-dimensional p-group fixed space

A matrix coefficient embeds a modular p-group representation into its regular
module if every fixed vector lies on a specified nonzero line. A nonzero kernel
would contain a fixed vector and would contradict the chosen coefficient.
Equality of dimensions then gives genuine equivariant regular coordinates.

This supplies the regular Sylow restriction of the Suzuki Steinberg tensor
without exposing the implementation of its existing root-norm proof.
-/

public noncomputable section
open Module Representation
namespace Representation.TwistedRegular

/-- A p-group module of its group order with exactly one fixed line is regular.
The coefficient map is injective because any nonzero kernel has a fixed vector. -/
theorem exists_regular_coordinates {k P V : Type*} [Field k] [Group P] [Fintype P]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k P V) (hc : ringChar k ≠ 0) (hp : IsPGroup (ringChar k) P)
    (z : V) (hz : z ≠ 0)
    (hfix : ∀ v, (∀ g, ρ g v = v) → ∃ c : k, v = c • z)
    (hd : finrank k V = Fintype.card P) :
    ∃ e : V ≃ₗ[k] (P → k), ∀ g v x, e (ρ g v) x = e v (g⁻¹ * x) := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hz
  let f : V →ₗ[k] (P → k) :=
    { toFun := fun v x => l (ρ x⁻¹ v)
      map_add' := by intro v w; ext x; simp
      map_smul' := by intro c v; ext x; simp }
  have heq (g : P) (v : V) (x : P) : f (ρ g v) x = f v (g⁻¹ * x) := by
    change l (ρ x⁻¹ (ρ g v)) = l (ρ (g⁻¹ * x)⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  let U : Subrepresentation ρ :=
    { toSubmodule := f.ker
      apply_mem_toSubmodule := by
        intro g v hv
        ext x
        change f (ρ g v) x = 0
        rw [heq]
        exact congrFun hv _ }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hn
    have hU : U.toSubmodule ≠ ⊥ := hn
    let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hU
    obtain ⟨v, hv, hfv⟩ := Representation.pGroup_fix_nonzero_vector hc hp U.toRepresentation
    obtain ⟨c, hc⟩ := hfix (v : V) (fun g => congrArg Subtype.val (hfv g))
    have hzero : l (v : V) = 0 := by
      have h := congrFun (show f (v : V) = 0 from v.property) 1
      change l (ρ (1 : P)⁻¹ (v : V)) = 0 at h
      simpa only [inv_one, map_one, Module.End.one_apply] using h
    have hc0 : c = 0 := by simpa [hc, hl] using hzero
    apply hv
    apply Subtype.ext
    simpa [hc0] using hc
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, ?_⟩, heq⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
  simpa using hd
end Representation.TwistedRegular

