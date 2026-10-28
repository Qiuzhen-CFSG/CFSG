module
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The symplectic normalizer of the binary determinant module

This is the literal intersection of the binary linear normalizer of
SL₂(4) × SL₂(4) with the isometries of a specified alternating form.
The form is retained: a linear normalizer alone also contains odd scalars.
These definitions provide the model boundary for the normalizer calculation
in Aschbacher--Smith 14.3.15, printed p.994, using G.11.2(7).
No index or order assertion is built into the definition.
-/

@[expose] public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Subgroup

/-- The actual normalizer inside the isometry group of B. -/
def symplecticNormalizer (B : LinearMap.BilinForm (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {t | t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) ∧
    ∀ u v, B (t u) (t v) = B u v}
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨mul_mem ha.1 hb.1, fun u v => (ha.2 (b u) (b v)).trans (hb.2 u v)⟩
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, fun u v => ?_⟩
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using
      (ha.2 (a.symm u) (a.symm v)).symm

theorem mem_symplecticNormalizer (B : LinearMap.BilinForm (ZMod 2) V)
    (t : V ≃ₗ[ZMod 2] V) : t ∈ symplecticNormalizer B ↔
      t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) ∧
        ∀ u v, B (t u) (t v) = B u v := Iff.rfl

instance (B : LinearMap.BilinForm (ZMod 2) V) : Finite (symplecticNormalizer B) := by
  let : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  infer_instance

end ClassicalOrthogonal.FourPlusMatrix.Binary
