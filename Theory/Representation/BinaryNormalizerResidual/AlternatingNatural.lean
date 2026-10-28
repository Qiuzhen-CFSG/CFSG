module
public import Theory.Representation.BinaryNormalizerResidual.TrivialCommutant
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import Theory.Representation.BinaryPermutation.SevenCommutant
public import Theory.Representation.BinaryPermutation.EightCommutant
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Alternating.Aut

/-!
# Two-residuals of natural binary alternating normalizers

For the five-, seven- and eight-letter natural modules, the checked scalar
commutant makes the linear centralizer trivial. Every alternating-group
automorphism in these degrees is induced by a permutation, so its outer
class has square one. The full linear normalizer therefore has its
two-residual inside the actual alternating action image.

The five-letter calculation is transported through the canonical
augmentation-core equivalence, retaining the literal natural quotient.
Source: Aschbacher–Smith, B.3.1 and 13.7.6, printed pp.83 and 940.
-/

public section
namespace Representation.BinaryNormalizerResidual
open Subgroup BinaryOffender BinaryPermutation

theorem alternating_outer_two (n : ℕ) (hn : 5 ≤ n) (hne : n ≠ 6) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  intro q
  obtain ⟨α, rfl⟩ :=
    QuotientGroup.mk'_surjective (MulAut.innerSubgroup (alternatingGroup (Fin n))) q
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hne).surjective α
  refine ⟨1, ?_⟩
  simp only [pow_one, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hσ : σ ^ 2 ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact ⟨⟨σ ^ 2, hσ⟩, MulAut.conjNormal_val.symm⟩

private theorem five_commutant (f : natural (Fin 5) ≃ₗ[ZMod 2] natural (Fin 5))
    (hf : ∀ (g : alternatingGroup (Fin 5)) v,
      f (naturalRepresentation (Fin 5) g.val v) = naturalRepresentation (Fin 5) g.val (f v)) :
    f = LinearEquiv.refl _ _ := by
  let e := coreEquivNatural (Fin 5) (by decide)
  have he (g : Equiv.Perm (Fin 5)) (v : core (Fin 5)) :
      e (coreRepresentation (Fin 5) g v) = naturalRepresentation (Fin 5) g (e v) :=
    coreEquivNatural_equivariant (Fin 5) (by decide) g v
  let F := e.trans (f.trans e.symm)
  have hF := FiveCentralExtension.core_commuting_eq_id F.toLinearMap (by
    intro g hg v
    apply e.injective
    change e (e.symm (f (e (coreRepresentation (Fin 5) g v)))) =
      e (coreRepresentation (Fin 5) g (e.symm (f (e v))))
    rw [e.apply_symm_apply, he, hf ⟨g,hg⟩, he, e.apply_symm_apply]) F.injective
  apply LinearEquiv.ext
  intro v
  change f v = v
  have hh := congrArg e (hF (e.symm v))
  change e (e.symm (f (e (e.symm v)))) = e (e.symm v) at hh
  simpa only [LinearEquiv.apply_symm_apply] using hh

theorem alternating_natural_residual_le (n : ℕ) (hn : n = 5 ∨ n = 7 ∨ n = 8) :
    (pResidual 2 (linearNormalizer (alternatingNaturalRepresentation (Ω := Fin n)))).map
      (linearNormalizer (alternatingNaturalRepresentation (Ω := Fin n))).subtype ≤
      actionImage (alternatingNaturalRepresentation (Ω := Fin n)) := by
  have hlarge : 5 ≤ n := by rcases hn with rfl | rfl | rfl <;> decide
  have hne : n ≠ 6 := by rcases hn with rfl | rfl | rfl <;> decide
  refine residual_le_of_trivial_commutant _ ?_ (alternating_outer_two n hlarge hne) ?_
  · intro g h he
    apply Subtype.ext
    exact naturalRepresentation_injective (Fin n) (by simpa using hlarge) he
  · intro f hf
    rcases hn with rfl | rfl | rfl
    · exact five_commutant f hf
    · have he := SevenCommutant.commuting_eq_id f.toLinearMap f.injective hf
      apply LinearEquiv.ext
      intro v
      exact LinearMap.congr_fun he v
    · exact EightCommutant.commuting_eq_refl f hf
end Representation.BinaryNormalizerResidual
