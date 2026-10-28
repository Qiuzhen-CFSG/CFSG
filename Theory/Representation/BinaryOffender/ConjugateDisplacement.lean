module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Degree bounds from conjugate generators

If n conjugates of an element generate a subgroup containing an actor with
zero fixed space, the representation embeds in the product of their n
displacement spaces. Conjugacy makes these spaces equidimensional, giving
dim V ≤ n codim C_V(t). This works over the original binary field, even for
operators that are semilinear over a larger field of definition.

This is the linear estimate preceding (2.6) in Guralnick–Malle,
Classification of 2F-modules I, manuscript p.4.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A finite family of conjugate generators bounds degree by displacement. -/
theorem finrank_le_mul_fixedCodim_of_conjugate_generation
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (hfix : fixedSpace ρ L = ⊥) (t : G) {n : ℕ} (g : Fin n → G)
    (hgen : L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹)) :
    Module.finrank (ZMod 2) V ≤ n * fixedCodim ρ (zpowers t) := by
  let δ (i : Fin n) : Module.End (ZMod 2) V := ρ (g i * t * (g i)⁻¹) - LinearMap.id
  let D : V →ₗ[ZMod 2] (∀ i : Fin n, LinearMap.range (δ i)) :=
    LinearMap.pi fun i => (δ i).rangeRestrict
  have hi : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot]
    apply le_bot_iff.mp
    intro v hv
    have hv' (i : Fin n) : ρ (g i * t * (g i)⁻¹) v = v := by
      have he := congrArg (fun f : ∀ i : Fin n, LinearMap.range (δ i) => (f i : V)) hv
      exact sub_eq_zero.mp he
    let T : Subgroup G := {
      carrier := {a | ρ a v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ a v = v at ha
        change ρ b v = v at hb
        change ρ (a * b) v = v
        simpa only [map_mul, Module.End.mul_apply, hb] using ha
      inv_mem' := by
        intro a ha
        have he : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rwa [ha] at he }
    have hT : closure (Set.range fun i => g i * t * (g i)⁻¹) ≤ T := by
      apply (closure_le T).mpr
      rintro _ ⟨i, rfl⟩
      exact hv' i
    have hvL : v ∈ fixedSpace ρ L := fun l => (hgen.trans hT) l.property
    simpa only [hfix, Submodule.mem_bot] using hvL
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have hδ (i : Fin n) : Module.finrank (ZMod 2) (LinearMap.range (δ i)) =
      fixedCodim ρ (zpowers t) := by
    rw [← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_conj]
  simpa only [Module.finrank_pi_fintype, hδ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hd

end Representation.BinaryOffender
