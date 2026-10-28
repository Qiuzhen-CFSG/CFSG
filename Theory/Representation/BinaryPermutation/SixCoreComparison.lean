module
public import Theory.Representation.BinaryPermutation.SixCoreNormalizer
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Comparing two augmentation-core markings

Two six-letter actions on the same group are permutation-conjugate if their
augmentation cores are intertwined and both map the same subgroup onto A₆.
Faithfulness identifies the component kernels. The induced automorphism of
A₆ and the full augmentation normalizer then identify the intertwiner with
one coordinate permutation, which conjugates the entire actions.

Source: Aschbacher--Smith B.3.1 and G.11.2(2), pp.83,364--367.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.SixCoreNormalizer

/-- Equivalent augmentation markings with the same alternating component
 differ by one permutation on the entire actor. -/
theorem conjugate_of_core_intertwiner {H : Type*} [Group H]
    (K : Subgroup H) (q p : H →* Equiv.Perm (Fin 6))
    (hq : K.map q = alternatingGroup (Fin 6))
    (hp : K.map p = alternatingGroup (Fin 6))
    (f : C ≃ₗ[ZMod 2] C)
    (hf : ∀ g v, f (coreRepresentation (Fin 6) (q g) v) =
      coreRepresentation (Fin 6) (p g) (f v)) :
    ∃ s : Equiv.Perm (Fin 6), ∀ g, p g = s * q g * s⁻¹ := by
  let a : K →* A := (q.comp K.subtype).codRestrict _
    (fun k => hq.le (mem_map_of_mem q k.property))
  let b : K →* A := (p.comp K.subtype).codRestrict _
    (fun k => hp.le (mem_map_of_mem p k.property))
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨k,hk,he⟩ := hq.ge x.property
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨k,hk,he⟩ := hp.ge x.property
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hker : a.ker = b.ker := by
    ext k
    change a k = 1 ↔ b k = 1
    have hi (g : Equiv.Perm (Fin 6)) :
        (∀ v, coreRepresentation (Fin 6) g v = v) → g = 1 := by
      intro hh
      apply action_injective
      apply LinearMap.ext
      intro v
      simpa only [map_one,Module.End.one_apply] using hh v
    constructor
    · intro hk
      apply Subtype.ext
      apply hi
      intro v
      obtain ⟨w,rfl⟩ := f.surjective v
      have hk' : q k = 1 := congrArg Subtype.val hk
      change coreRepresentation (Fin 6) (p k) (f w) = f w
      simpa only [hk',map_one,Module.End.one_apply] using (hf k w).symm
    · intro hk
      apply Subtype.ext
      apply hi
      intro v
      apply f.injective
      have hk' : p k = 1 := congrArg Subtype.val hk
      change f (coreRepresentation (Fin 6) (q k) v) = f v
      simpa only [hk',map_one,Module.End.one_apply] using hf k v
  let ea := QuotientGroup.quotientKerEquivOfSurjective a ha
  let eb := QuotientGroup.quotientKerEquivOfSurjective b hb
  let φ : MulAut A := ea.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans eb)
  have hφ (k : K) : φ (a k) = b k := by
    change eb ((QuotientGroup.quotientMulEquivOfEq hker) (ea.symm (ea (QuotientGroup.mk k)))) = _
    rw [ea.symm_apply_apply,QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  obtain ⟨s,hs⟩ := normalizer f φ (by
    intro x v
    obtain ⟨k,rfl⟩ := ha x
    rw [hφ]
    exact hf k v)
  refine ⟨s,fun g => ?_⟩
  apply action_injective
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := f.surjective v
  rw [←hf,hs,hs]
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

end BinaryPermutation.SixCoreNormalizer
