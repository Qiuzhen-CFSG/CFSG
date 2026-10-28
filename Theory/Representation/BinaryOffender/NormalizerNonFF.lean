module

public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Non-FF actions from a marked normal model

Conjugating a faithful action through coordinates for a normal marked
subgroup embeds the entire ambient group into the model's full linear
normalizer. The embedding preserves the original elementary actor, its rank
and its fixed codimension. Non-FF of the full model normalizer therefore
implies non-FF for the ambient action, without a finiteness assumption.

The source application is the A-invariant natural determinant section in
Aschbacher–Smith D.3.9, printed pp.199–200. A surjective marking accommodates
the literal local quotient and either marking of each component.
-/

@[expose] public section
namespace Representation.BinaryOffender
open Subgroup
variable {H K P V W : Type*} [Group H] [Group K] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A marked normal model whose full normalizer is non-FF excludes every
faithful ambient FF action on the same module. -/
theorem not_isFFModule_of_marked_normal_range
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (hμ : ¬ IsFFModule (normalizerRepresentation μ)) : ¬ IsFFModule ρ := by
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
  intro h
  exact hμ (h.map_equivariant ρ (normalizerRepresentation μ) j hj E he)

/-- Passing first to the faithful action image removes the faithfulness
premise on the original ambient group. -/
theorem not_isFFModule_image_of_marked_normal_range
    (ρ : Representation (ZMod 2) H V) (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (hμ : ¬ IsFFModule (normalizerRepresentation μ)) :
    ¬ IsFFModule (imageRepresentation ρ) := by
  let j : K →* actionImage ρ := (actionHom ρ).comp i
  have hj : j.range = i.range.map (actionHom ρ) := MonoidHom.range_comp _ _
  let : j.range.Normal := by
    rw [hj]
    exact Subgroup.Normal.map inferInstance (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  let b' : Representation.Equiv ((imageRepresentation ρ).comp j) (μ.comp f) :=
    { __ := b.toLinearEquiv
      isIntertwining' k := by
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap k v }
  exact not_isFFModule_of_marked_normal_range (imageRepresentation ρ)
    (imageRepresentation_injective ρ) j μ f hf b' hμ

end Representation.BinaryOffender
