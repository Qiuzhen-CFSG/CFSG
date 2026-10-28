module

public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.SL2SevenCentralProductOffenders

/-!
# Degree bounds from three conjugates in the full linear normalizer

The displacement spaces of three conjugates span every nontrivial faithful
irreducible component module when those conjugates generate a subgroup containing
the component image. Their dimensions agree. An FF offender supplies an involution
of displacement at most the automorphism two-rank, so the whole degree is at most
three times that rank.

This uses the literal image inside its full linear normalizer. The generation
condition is an explicit group-theoretic input; it is not asserted for arbitrary
components. Source application: Aschbacher–Smith B.1.13, printed pp.73–74.
-/

@[expose] public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Three conjugate involutions generate a subgroup containing the literal image. -/
def NormalizerThreeConjugates : Prop :=
  ∀ t : linearNormalizer ρ, t ≠ 1 → t ^ 2 = 1 →
    ∃ g h : linearNormalizer ρ,
      (actionImage ρ).subgroupOf (linearNormalizer ρ) ≤
        zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹)

/-- A faithful nontrivial irreducible action is spanned by its displacements. -/
theorem subspaceCommutator_top_eq_top_of_faithful_irreducible [Nontrivial G]
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible) :
    subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let D := subspaceCommutator ρ ⊤ ⊤
  let R : Subrepresentation ρ := {
    toSubmodule := D
    apply_mem_toSubmodule := by
      intro g
      change D ≤ D.comap (ρ g)
      apply Submodule.span_le.mpr
      rintro _ ⟨h, _, v, _, rfl⟩
      change ρ g (ρ h v - v) ∈ D
      have hgh : ρ (g * h) v - v ∈ D :=
        Submodule.subset_span ⟨g * h, mem_top _, v, Submodule.mem_top, rfl⟩
      have hg : ρ g v - v ∈ D :=
        Submodule.subset_span ⟨g, mem_top _, v, Submodule.mem_top, rfl⟩
      have he : ρ g (ρ h v - v) = (ρ (g * h) v - v) - (ρ g v - v) := by
        rw [map_sub, map_mul, Module.End.mul_apply]
        abel
      rw [he]
      exact D.sub_mem hgh hg }
  rcases hi.eq_bot_or_eq_top R with hz | ht
  · have hD : D = ⊥ := congrArg Subrepresentation.toSubmodule hz
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exfalso
    apply hg
    apply hf
    rw [map_one]
    ext v
    have hv : ρ g v - v ∈ D :=
      Submodule.subset_span ⟨g, mem_top _, v, Submodule.mem_top, rfl⟩
    rw [hD, Submodule.mem_bot] at hv
    exact sub_eq_zero.mp hv
  · exact congrArg Subrepresentation.toSubmodule ht

/-- The same spanning statement inside the full normalizer, on the same space. -/
theorem normalizerImage_subspaceCommutator_eq_top [Nontrivial G]
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible) :
    subspaceCommutator (normalizerRepresentation ρ) ⊤
      ((actionImage ρ).subgroupOf (linearNormalizer ρ)) = ⊤ := by
  apply top_unique
  calc
    ⊤ = subspaceCommutator ρ ⊤ ⊤ :=
      (subspaceCommutator_top_eq_top_of_faithful_irreducible ρ hf hi).symm
    _ ≤ _ := ?_
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, v, _, rfl⟩
  let x : linearNormalizer ρ :=
    ⟨ρ.asGroupHom g, (actionImage ρ).le_normalizer (show ρ.asGroupHom g ∈ actionImage ρ from ⟨g, rfl⟩)⟩
  exact Submodule.subset_span ⟨x, ⟨g, rfl⟩, v, Submodule.mem_top, rfl⟩

/-- An FF normalizer has degree at most three times its image's automorphism rank
when the explicit three-conjugate generation condition holds. -/
theorem finrank_le_of_ff_normalizer_three_conjugates [Nontrivial G]
    [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hgen : NormalizerThreeConjugates ρ)
    (hff : IsFFModule (normalizerRepresentation ρ)) :
    Module.finrank (ZMod 2) V ≤ 3 * primeRank 2 (MulAut (actionImage ρ)) := by
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_displacement_involution ρ hi hff
  obtain ⟨g, h, hgh⟩ := hgen t ht ht2
  exact (SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    (normalizerRepresentation ρ) _ (normalizerImage_subspaceCommutator_eq_top ρ hf hi)
    t g h hgh).trans (Nat.mul_le_mul_left 3 hd)

end Representation.BinaryOffender
