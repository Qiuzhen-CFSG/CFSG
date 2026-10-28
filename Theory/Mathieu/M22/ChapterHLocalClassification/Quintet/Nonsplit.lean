module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Nonsplit.FixedVectors
public import Theory.LinearAlgebra.RegularLinearAction
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Indecomposability of the actual outer quintet translation action

The inner E16 embeds equivariantly in the outer E32 by literal subgroup
inclusion. Assume the inner conjugation module is irreducible. The inverse
image of a subrepresentation is then zero or the whole inner module. In
the first case the dimension formula bounds that subrepresentation by one;
a binary line is fixed pointwise, so the native fixed-vector calculation
makes it zero. Thus every nonzero subrepresentation contains the inner
module, and two nonzero subrepresentations cannot be complementary.

This proves the candidate-module nonsplitting branch of Aschbacher--Smith
H.14.3(2), printed p.397, combined manuscript of 1 March 2004. Inner
irreducibility is the explicit input from the independent natural-module
calculation. Identification with the intrinsic core and transport through
the actual five-part S5 quotient remain with the source-theorem assembly.
The finite hexacode calculation and its ATLAS attribution are in
`Nonsplit.FixedVectors`.
-/

@[expose] public section

noncomputable section
open scoped IsMulCommutative
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.M22Quintet
namespace Sporadic.Mathieu.M22ChapterH.Quintet

/-- Literal inclusion of the inner translations in the outer translations. -/
def innerTranslationInclusion :
    Representation.IntertwiningMap innerTranslationConjugation outerTranslationConjugation where
  toLinearMap := (Subgroup.inclusion (show innerTranslationGroup ≤ outerTranslationGroup from
    inf_le_left)).toAdditive.toZModLinearMap 2
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

@[simp] theorem innerTranslationInclusion_apply (v : Additive innerTranslationGroup) :
    (innerTranslationInclusion v).toMul.val = v.toMul.val := rfl

theorem innerTranslationInclusion_injective : Function.Injective innerTranslationInclusion := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun v : Additive outerTranslationGroup => v.toMul.val) h

theorem innerTranslationInclusion_finrank :
    Module.finrank (ZMod 2) innerTranslationInclusion.range.toSubmodule = 4 := by
  rw [Representation.IntertwiningMap.range_toSubmodule,
    LinearMap.finrank_range_of_inj innerTranslationInclusion_injective,
    innerTranslationGroup_finrank]

private theorem small_subrepresentation_bot
    (hfixed : ∀ v : Additive outerTranslationGroup,
      (∀ g : Q, outerTranslationConjugation g v = v) → v = 0)
    (A : Subrepresentation outerTranslationConjugation)
    (hdim : Module.finrank (ZMod 2) A.toSubmodule ≤ 1) : A = ⊥ := by
  apply bot_unique
  intro v hv
  apply hfixed v
  intro g
  have he := LinearGroup.eq_one_of_binary_finrank_le_one hdim
    (LinearMap.GeneralLinearGroup.toLinearEquiv (A.toRepresentation.asGroupHom g))
  exact congrArg Subtype.val (LinearEquiv.congr_fun he ⟨v, hv⟩)

private theorem subrepresentation_bot_or_contains_inner
    (hinner : Representation.IsIrreducible innerTranslationConjugation)
    (hfixed : ∀ v : Additive outerTranslationGroup,
      (∀ g : Q, outerTranslationConjugation g v = v) → v = 0)
    (A : Subrepresentation outerTranslationConjugation) :
    A = ⊥ ∨ innerTranslationInclusion.range ≤ A := by
  let I : Subrepresentation innerTranslationConjugation := {
    toSubmodule := A.toSubmodule.comap innerTranslationInclusion.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      change innerTranslationInclusion (innerTranslationConjugation g v) ∈ A
      rw [innerTranslationInclusion.isIntertwining]
      exact A.apply_mem_toSubmodule g hv }
  rcases hinner.eq_bot_or_eq_top I with hI | hI
  · left
    have hdis : innerTranslationInclusion.range.toSubmodule ⊓ A.toSubmodule = ⊥ := by
      apply bot_unique
      rintro v ⟨⟨w, rfl⟩, hw⟩
      have hz : w ∈ I := hw
      rw [hI] at hz
      have hz' : w = 0 := hz
      rw [hz', map_zero]
      exact Submodule.zero_mem _
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      innerTranslationInclusion.range.toSubmodule A.toSubmodule
    rw [hdis, finrank_bot, innerTranslationInclusion_finrank] at hdim
    have hle := (innerTranslationInclusion.range.toSubmodule ⊔ A.toSubmodule).finrank_le
    rw [outerTranslationGroup_finrank] at hle
    exact small_subrepresentation_bot hfixed A (by omega)
  · right
    rintro v ⟨w, rfl⟩
    have hw : w ∈ I := by rw [hI]; trivial
    exact hw

/-- Complementary subrepresentations of the native outer translation action
have a zero summand, assuming the inner action is irreducible. -/
theorem outerTranslationConjugation_indecomposable
    (hinner : Representation.IsIrreducible innerTranslationConjugation)
    (A B : Subrepresentation outerTranslationConjugation) (hAB : IsCompl A B) :
    A = ⊥ ∨ B = ⊥ := by
  rcases subrepresentation_bot_or_contains_inner hinner
    outerTranslationConjugation_fixed_eq_zero A with ha | ha
  · exact Or.inl ha
  rcases subrepresentation_bot_or_contains_inner hinner
    outerTranslationConjugation_fixed_eq_zero B with hb | hb
  · exact Or.inr hb
  have he : innerTranslationInclusion.range = ⊥ :=
    bot_unique ((le_inf ha hb).trans hAB.disjoint.le_bot)
  have hd := innerTranslationInclusion_finrank
  have he' : innerTranslationInclusion.range.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule he
  rw [he', finrank_bot] at hd
  omega

end Sporadic.Mathieu.M22ChapterH.Quintet
