module
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Marked normalizer residuals contain the actual prime-perfect actor

A faithful ambient action normalizing a marked component embeds into the
component's full linear normalizer. If the two-residual of that normalizer
lies in the component image, every two-perfect ambient subgroup lies in
the original component. All containments use the supplied action marking.

The source consumer applies this to the literal point residual in original
13.7.6, without assuming the later containment of13.7.19.
Source: Aschbacher--Smith, printed pp.938--940.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {H B E : Type*} [Group H] [Group B] [AddCommGroup E] [Module (ZMod 2) E]

/-- A marked model normalizer bounds the original two-perfect subgroup. -/
theorem le_normal_of_marked_normalizer_residual
    (γ : Representation (ZMod 2) H E) (hγ : Function.Injective γ)
    (K : Subgroup H) [K.Normal] (e : K ≃* B)
    (τ : Representation (ZMod 2) B E)
    (hres : ∀ (k : K) v, γ k v = τ (e k) v)
    (hmodel : (pResidual 2 (linearNormalizer τ)).map (linearNormalizer τ).subtype ≤
      actionImage τ)
    (J : Subgroup H) (hJ : IsPPerfect 2 J) : J ≤ K := by
  let a := γ.asGroupHom
  have ha : Function.Injective a := fun _ _ he => hγ (congrArg Units.val he)
  have hm : K.map a = actionImage τ := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      refine ⟨e ⟨k,hk⟩,?_⟩
      apply Units.ext
      ext v
      exact (hres ⟨k,hk⟩ v).symm
    · rintro ⟨b,rfl⟩
      refine ⟨e.symm b,(e.symm b).property,?_⟩
      apply Units.ext
      ext v
      change γ (e.symm b) v = τ b v
      simpa only [e.apply_symm_apply] using hres (e.symm b) v
  have hn (g : H) : a g ∈ linearNormalizer τ := by
    change a g ∈ normalizer (actionImage τ : Set _)
    rw [←hm]
    exact K.le_normalizer_map a (mem_map_of_mem a
      (show g ∈ normalizer (K : Set H) from le_normalizer_of_normal (mem_top g)))
  let f : H →* linearNormalizer τ := a.codRestrict _ hn
  have hp : J.map f ≤ pResidual 2 (linearNormalizer τ) :=
    le_pResidual_of_isPPerfect _ (hJ.of_surjective (f.subgroupMap J)
      (f.subgroupMap_surjective J))
  intro j hj
  have hh := hmodel (mem_map_of_mem (linearNormalizer τ).subtype
    (hp (mem_map_of_mem f hj)))
  change a j ∈ actionImage τ at hh
  rw [←hm] at hh
  obtain ⟨k,hk,hkj⟩ := hh
  exact ha hkj ▸ hk
end Representation.BinaryOffender
