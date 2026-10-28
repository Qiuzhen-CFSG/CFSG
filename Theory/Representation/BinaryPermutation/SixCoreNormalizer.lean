module
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer
public import Theory.Representation.BinaryPermutation.SixCommutant
public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Normalizers of the six-letter augmentation core

A twisted automorphism preserves the constant line, since it is exactly the
fixed space of A₆. Its induced automorphism on the natural quotient lies in
the natural S₆. Removing that permutation from the original five-dimensional
map leaves an A₆-commuting automorphism, which is the identity. Thus the full
normalizer acts by actual coordinate permutations on the augmentation core;
no four-dimensional subgroup or splitting of the core is required.

Source: Aschbacher–Smith B.3.1 and G.11.2(2), printed pp.83,364–367;
used for the original five-dimensional setup of 13.2.2 and 13.4.10.
-/

public noncomputable section
namespace BinaryPermutation.SixCoreNormalizer
open Subgroup
abbrev C := core (Fin 6)
abbrev A := alternatingGroup (Fin 6)

private theorem kernel_iff_fixed (v : C) :
    v ∈ (coreToNatural (Fin 6)).ker ↔
      ∀ a : A, coreRepresentation (Fin 6) a.val v = v := by
  rw [core_fixed_iff_constant (by simp)]
  change coreToNatural (Fin 6) v = 0 ↔ _
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

private theorem kernel_map (f : C ≃ₗ[ZMod 2] C) (φ : MulAut A)
    (hf : ∀ a v, f (coreRepresentation (Fin 6) a.val v) =
      coreRepresentation (Fin 6) (φ a).val (f v)) :
    (coreToNatural (Fin 6)).ker.map f.toLinearMap = (coreToNatural (Fin 6)).ker := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hw := (kernel_iff_fixed w).mp hw
    apply (kernel_iff_fixed (f w)).mpr
    intro a
    obtain ⟨a,rfl⟩ := φ.surjective a
    rw [←hf,hw]
  · intro hv
    refine ⟨f.symm v,?_,f.apply_symm_apply v⟩
    have hv := (kernel_iff_fixed v).mp hv
    apply (kernel_iff_fixed (f.symm v)).mpr
    intro a
    apply f.injective
    rw [hf,f.apply_symm_apply,hv]

/-- A twisted automorphism of the five-dimensional core induces a natural
permutation automorphism of A₆. The quotient is taken only inside this proof. -/
theorem natural_of_intertwiner (f : C ≃ₗ[ZMod 2] C) (φ : MulAut A)
    (hf : ∀ a v, f (coreRepresentation (Fin 6) a.val v) =
      coreRepresentation (Fin 6) (φ a).val (f v)) :
    φ ∈ AlternatingSix.ShadowLocal.natural := by
  let p := coreToNatural (Fin 6)
  let e := p.quotKerEquivOfSurjective coreToNatural_surjective
  let b := Submodule.Quotient.equiv p.ker p.ker f (kernel_map f φ hf)
  let u := e.symm.trans (b.trans e)
  have hu (v : C) : u (p v) = p (f v) := by
    change e (b (e.symm (e (Submodule.Quotient.mk v)))) = _
    rw [e.symm_apply_apply]
    rfl
  apply Representation.BinaryAlternatingSixNaturalNormalizer.natural_of_intertwiner φ u
  intro a v
  obtain ⟨v,rfl⟩ := coreToNatural_surjective v
  change u (naturalRepresentation (Fin 6) a.val (p v)) =
    naturalRepresentation (Fin 6) (φ a).val (u (p v))
  rw [←coreToNatural_equivariant,hu,hf,coreToNatural_equivariant,hu]

/-- The full normalizer of the marked augmentation action consists of
actual six-letter permutations, on the original five-dimensional module. -/
theorem normalizer (f : C ≃ₗ[ZMod 2] C) (φ : MulAut A)
    (hf : ∀ a v, f (coreRepresentation (Fin 6) a.val v) =
      coreRepresentation (Fin 6) (φ a).val (f v)) :
    ∃ s : Equiv.Perm (Fin 6), ∀ v, f v = coreRepresentation (Fin 6) s v := by
  obtain ⟨s,hs⟩ := natural_of_intertwiner f φ hf
  have hφ (a : A) : (φ a).val = s * a.val * s⁻¹ := by
    exact (congrArg (fun α : MulAut A => (α a).val) hs).symm
  let r := coreRepresentation (Fin 6)
  let es := LinearEquiv.ofBijective (r s⁻¹) (r.apply_bijective s⁻¹)
  let F := f.trans es
  have hF : F = LinearEquiv.refl _ _ := by
    apply SixCommutant.commuting_eq_refl
    intro a v
    change r s⁻¹ (f (r a.val v)) = r a.val (r s⁻¹ (f v))
    rw [hf,hφ]
    dsimp only [r]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left]
  refine ⟨s,fun v => ?_⟩
  have hh := congrArg (r s) (LinearEquiv.congr_fun hF v)
  change r s (r s⁻¹ (f v)) = r s v at hh
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply] using hh
/-- Faithfulness on all six-letter permutations, with the original core. -/
theorem action_injective : Function.Injective (coreRepresentation (Fin 6)) := by
  intro a b hab
  apply naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := coreToNatural_surjective w
  rw [←coreToNatural_equivariant,←coreToNatural_equivariant]
  exact congrArg (coreToNatural (Fin 6)) (DFunLike.congr_fun hab v)
end BinaryPermutation.SixCoreNormalizer
