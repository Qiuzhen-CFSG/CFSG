module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer

/-!
# Uniqueness of the deleted-module extension

The A₅-equivariant identification of the four-dimensional deleted module
intertwines every element of its given overgroup in S₅. Indeed the difference
between the two actions commutes with A₅; its scalar commutant over F₂ and
invertibility force that difference to be the identity.

This supplies the extension-action step in the deleted branch of
Aschbacher–Smith 14.4.10, printed p.1010, under case 14.4.2(5).
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The given A₅ identification extends to the entire specified overgroup. -/
theorem deleted_extension_equivariant
    (σ : Representation (ZMod 2) D V)
    (f : V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (hf : ∀ (a : AltFive) (v : V), f (σ (inclusion hAD a) v) =
      BinaryPermutation.coreRepresentation (Fin 5) a.val (f v))
    (d : D) (v : V) : f (σ d v) =
      BinaryPermutation.coreRepresentation (Fin 5) d.val (f v) := by
  let τ := BinaryPermutation.coreRepresentation (Fin 5)
  let F : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] BinaryPermutation.core (Fin 5) :=
    (τ d.val⁻¹).comp (f.toLinearMap.comp ((σ d).comp f.symm.toLinearMap))
  have hcomm (a : AltFive) (w : BinaryPermutation.core (Fin 5)) :
      F (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a w) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) a (F w) := by
    let b : AltFive := ⟨d.val * a.val * d.val⁻¹,
      (inferInstance : AltFive.Normal).conj_mem a.val a.property d.val⟩
    have hinv : f.symm (τ a.val w) = σ (inclusion hAD a) (f.symm w) := by
      apply f.injective
      rw [f.apply_symm_apply, hf, f.apply_symm_apply]
    have hprod : d * inclusion hAD a = inclusion hAD b * d := by
      apply Subtype.ext
      change d.val * a.val = (d.val * a.val * d.val⁻¹) * d.val
      group
    change τ d.val⁻¹ (f (σ d (f.symm (τ a.val w)))) =
      τ a.val (τ d.val⁻¹ (f (σ d (f.symm w))))
    rw [hinv, ← Module.End.mul_apply, ← map_mul, hprod, map_mul,
      Module.End.mul_apply, hf]
    change τ d.val⁻¹ (τ (d.val * a.val * d.val⁻¹) _) = τ a.val (τ d.val⁻¹ _)
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  obtain ⟨c, hc⟩ := BinaryPermutation.FiveTensorNormalizer.core_commuting_scalar F hcomm
  have hinj : Function.Injective F :=
    (τ.apply_bijective _).injective.comp
      (f.injective.comp ((σ.apply_bijective _).injective.comp f.symm.injective))
  have hc0 : c ≠ 0 := by
    intro he
    let z : BinaryPermutation.core (Fin 5) := ⟨![1,1,0,0,0], by
      rw [BinaryPermutation.mem_core]; decide⟩
    have hz : z ≠ 0 := by decide
    apply hz
    apply hinj
    rw [hc, he, zero_smul, map_zero]
  have hc1 : c = 1 := by
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact (hb c).resolve_left hc0
  have he := hc (f v)
  rw [hc1, one_smul] at he
  change τ d.val⁻¹ (f (σ d (f.symm (f v)))) = f v at he
  rw [f.symm_apply_apply] at he
  have hh := congrArg (τ d.val) he
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
