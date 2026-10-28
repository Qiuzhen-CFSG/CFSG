module

public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# Degree restrictions on each offender in a full binary normalizer

Conjugate generation bounds the degree by the displacement of every nonidentity
normalizing involution. Each element of an offender fixes its common fixed
space, so its displacement is at most the rank of that particular offender.
Consequently `dim V ≤ n * rank A` for every offender A, not only for a selected
one. This restricts the elementary subgroups needing a small-module calculation.

The application is the full linear normalizer in Aschbacher–Smith B.1.13,
printed pp.73–74 / PDF pp.84–85 of `refs/quasithin.pdf`. No numerical generation
bound or classification of modules is assumed to have been proved here.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every element of an offender moves at most the rank of that offender. -/
theorem IsOffender.fixedCodim_zpowers_le_rank (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} (hA : IsOffender ρ A) {a : G} (ha : a ∈ A) :
    fixedCodim ρ (zpowers a) ≤ rank A := by
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) := by
    intro v hv b
    exact hv ⟨b, (zpowers_le.mpr ha) b.property⟩
  have hd := Submodule.finrank_mono hfix
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank ρ (zpowers a)
  have h₃ := hA.2
  omega

/-- The conjugate estimate applies to each actual normalizing involution. -/
theorem finrank_le_mul_fixedCodim_of_normalizer_involution [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) {n : ℕ}
    (hgen : NormalizerConjugateGenerationBound ρ n)
    (t : linearNormalizer ρ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Module.finrank (ZMod 2) V ≤
      n * fixedCodim (normalizerRepresentation ρ) (zpowers t) := by
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  have hfix : fixedSpace τ (actionImage ρ) = ⊥ := by
    have he : fixedSpace τ (actionImage ρ) = ρ.invariants := by
      ext v
      constructor
      · intro h g
        exact h ⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩
      · rintro h ⟨_, g, rfl⟩
        exact h g
    rw [he, invariants_eq_bot_of_faithful_irreducible ρ hf hi]
  obtain ⟨c, hc⟩ := hgen t ht ht2
  have hd := finrank_le_mul_fixedCodim_of_conjugates τ (actionImage ρ) hfix t.val c hc
  have he : fixedCodim τ (zpowers t.val) =
      fixedCodim (normalizerRepresentation ρ) (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rwa [he] at hd

/-- Each offender separately has rank at least the degree divided by the
number of conjugates. The original action need not have finite domain. -/
theorem finrank_le_mul_rank_of_normalizer_offender [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) {n : ℕ}
    (hgen : NormalizerConjugateGenerationBound ρ n)
    {A : Subgroup (linearNormalizer ρ)}
    (hA : IsOffender (normalizerRepresentation ρ) A) :
    Module.finrank (ZMod 2) V ≤ n * rank A := by
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  exact (finrank_le_mul_fixedCodim_of_normalizer_involution ρ hf hi hgen t ht1
    (elemPow_eq_one_of_isElementaryAbelian t ht)).trans
      (Nat.mul_le_mul_left n (IsOffender.fixedCodim_zpowers_le_rank _ hA ht))

end Representation.BinaryOffender
