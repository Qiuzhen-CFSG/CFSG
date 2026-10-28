module
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements

/-!
# Normal extensions of a binary A₇ four-space

Self-normalization of the faithful A₇ image forces every operator in a
normal extension to belong to that image. A nontrivial involutory operator
therefore moves a plane, by the actual four-space involution calculation.
This applies to the original YT action in the last branch of 12.2.19.

Source: Aschbacher–Smith, C.1.23(2) and 12.2.19, printed pp.130,802.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryAlternatingSevenControl
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Every operator extending a normal faithful A₇ four-space is an A₇ operator. -/
theorem exists_operator_of_normal_extension
    {J : Type*} [Group J] (τ : Representation (ZMod 2) J W)
    (K : Subgroup J) [K.Normal]
    (ρ : Representation (ZMod 2) A7 W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4)
    (f : K →* A7) (hs : Function.Surjective f)
    (he : ∀ k : K, τ k = ρ (f k)) (g : J) : ∃ a : A7, τ g = ρ a := by
  have hi : actionImage (τ.comp K.subtype) = actionImage ρ := by
    ext u
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨f k, Units.ext (he k).symm⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨k,rfl⟩ := hs a
      exact ⟨k, Units.ext (he k)⟩
  have hn := actionImage_le_linearNormalizer τ K
  change actionImage τ ≤ normalizer (actionImage (τ.comp K.subtype) : Set _) at hn
  rw [hi, actionImage_self_normalizing ρ hf hd] at hn
  obtain ⟨a,ha⟩ := hn (show τ.asGroupHom g ∈ actionImage τ from ⟨g,rfl⟩)
  exact ⟨a,(congrArg Units.val ha).symm⟩

/-- A moving involution in such an extension has a two-dimensional moved space. -/
theorem displacement_finrank_of_normal_extension
    {J : Type*} [Group J] (τ : Representation (ZMod 2) J W)
    (K : Subgroup J) [K.Normal]
    (ρ : Representation (ZMod 2) A7 W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4)
    (f : K →* A7) (hs : Function.Surjective f)
    (he : ∀ k : K, τ k = ρ (f k))
    (g : J) (hg : g ^ 2 = 1) (hn : τ g ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (τ g - LinearMap.id)) = 2 := by
  obtain ⟨a,ha⟩ := exists_operator_of_normal_extension τ K ρ hf hd f hs he g
  have ha2 : a ^ 2 = 1 := by
    apply hf
    rw [map_pow, ←ha, ←map_pow, hg, map_one, map_one]
  have ha1 : a ≠ 1 := by intro h; exact hn (ha.trans (h ▸ ρ.map_one))
  rw [ha, ←fixedCodim_zpowers_eq_displacement_rank]
  exact AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hf hd a
    (orderOf_eq_prime ha2 ha1)

end Representation.BinaryAlternatingSevenControl
