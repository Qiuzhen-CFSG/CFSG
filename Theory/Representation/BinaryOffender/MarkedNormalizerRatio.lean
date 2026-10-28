module
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Quadratic ratios from a marked normal subgroup

Coordinates for a normally embedded model put the faithful ambient actor
inside the full linear normalizer of that model. Equivariant transport
preserves every elementary quadratic actor and its ratio, so the ambient
quadratic ratio is at least the full normalizer's ratio.

This retains the literal marked quotient and is used in the source tensor
application of the conjugate-generator inequality D.1.3(b), printed
pp.173--174, of Aschbacher--Smith.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {H K P V W : Type*} [Group H] [Group K] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem quadraticRatio_le_of_marked_normal_range
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f)) :
    quadraticRatio (normalizerRepresentation μ) ≤ quadraticRatio ρ := by
  let E := b.toLinearEquiv
  let γ : Representation (ZMod 2) H W := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : V) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (k : K) : γ (i k) = μ (f k) := by
    ext w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← he]
    exact Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap k v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨k,rfl⟩,rfl⟩
      exact ⟨f k,Units.ext (hres k).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨k,rfl⟩ := hf p
      exact ⟨i k,⟨k,rfl⟩,Units.ext (hres k)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  exact quadraticRatio_le_of_injective_equivariant ρ (normalizerRepresentation μ) j hj E he

end Representation.BinaryOffender
