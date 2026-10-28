module
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Cubic bounds in a marked model normalizer

A faithful ambient action whose normal subgroup has a specified model embeds
in that model's full linear normalizer after conjugating by the supplied
linear coordinates. The embedding preserves the original elementary actor
and its rank. Consequently a strict displacement bound for all elementary
normalizer actors excludes an ambient cubic bound at the same threshold.

The moved A₅ pair application uses this for the literal local faithful actor;
no elementary subgroup is lifted through a quotient.
-/
@[expose] public section
open Subgroup
namespace Representation.BinaryOffender
variable {H K P V W : Type*} [Group H] [Group K] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A faithful action with a normally embedded marked model retains its
cubic bound in the model's full linear normalizer. -/
theorem cubicRatio_normalizer_le_of_marked_normal_range
    [Finite H] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (n : ℕ) (hb : cubicRatio ρ ≤ n) :
    cubicRatio (normalizerRepresentation μ) ≤ n := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) W) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let E := b.toLinearEquiv
  let γ : Representation (ZMod 2) H W := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : V) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (k : K) : γ (i k) = μ (f k) := by
    ext w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [←he]
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
    rw [←himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  exact cubicRatio_le_nat_of_equivariant ρ (normalizerRepresentation μ) j hj E
    (fun g v => he g v) n hb

/-- Strict elementary-actor displacement in the model normalizer excludes
an actual faithful ambient action of bounded cubic ratio. -/
theorem not_cubicRatio_le_of_marked_normal_range
    [Finite H] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (n : ℕ)
    (hstrict : ∀ A : Subgroup (linearNormalizer μ), IsElementaryTwo A →
      n * rank A < fixedCodim (normalizerRepresentation μ) A) :
    ¬ cubicRatio ρ ≤ n := by
  intro hb
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) W) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hn := cubicRatio_normalizer_le_of_marked_normal_range ρ hρ i μ f hf b n hb
  obtain ⟨A,hA,_,ha⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation μ) n).mp hn
  exact (not_le_of_gt (hstrict A hA)) ha
end Representation.BinaryOffender
