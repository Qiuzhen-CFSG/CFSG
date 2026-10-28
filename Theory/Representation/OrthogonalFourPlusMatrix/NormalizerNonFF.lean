module

public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActors
public import Theory.Representation.OrthogonalFourPlusMatrix.ElementaryNormalizerGeometry
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# The natural determinant tensor is non-FF under its full normalizer

Every nontrivial elementary subgroup in the full binary linear normalizer
of the eight-dimensional determinant module moves more dimensions than its
rank. Rank at most two follows from the pointwise stabilizer of a quadratic
hyperplane; rank three supplies an inner involution moving four dimensions;
rank four supplies independently supported inner involutions with common
fixed codimension at least six. Conjugation bounds the elementary rank by
four, since the scalar centralizer has no involutions.

The final applications retain a literal normally embedded marked model in
an arbitrary ambient section action and pass to its faithful action image.
This discharges the natural-tensor non-FF input in Aschbacher–Smith D.3.9,
printed pp.199–200, without imposing faithfulness on the ambient section.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender

/-- Every nontrivial elementary actor in the entire binary normalizer moves
strictly more dimensions than its rank. -/
theorem normalizer_rank_lt_fixedCodim
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) :
    rank A < fixedCodim (normalizerRepresentation action) A := by
  have hr := elementary_normalizer_rank_le_four A hA
  by_cases hfour : 4 ≤ rank A
  · have hh := fixedCodim_ge_six_of_rank_ge_four A hA hfour
    omega
  by_cases hthree : 3 ≤ rank A
  · have hh := fixedCodim_ge_four_of_rank_ge_three A hA hthree
    omega
  by_cases htwo : 2 ≤ rank A
  · by_contra! hh
    have hs : fixedCodim (normalizerRepresentation action) A ≤ 2 := by omega
    have hsmall := rank_le_one_of_fixedCodim_le_two A hA hs
    omega
  have hh := fixedCodim_ge_two_of_nontrivial A hA.1
  omega

/-- The full binary linear normalizer of the natural determinant tensor
module is non-FF. -/
theorem normalizer_not_ff : ¬ IsFFModule (normalizerRepresentation action) := by
  rintro ⟨A,hA,hh⟩
  exact (not_le_of_gt (normalizer_rank_lt_fixedCodim A hA)) hh

variable {H K W : Type*} [Group H] [Group K]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A literal marked normal determinant action is non-FF after passage to
the faithful ambient action image, allowing arbitrary section kernels. -/
theorem image_not_ff_of_marked_normal_range
    (ρ : Representation (ZMod 2) H W) (i : K →* H) [i.range.Normal]
    (f : K →* G) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (action.comp f)) :
    ¬ IsFFModule (imageRepresentation ρ) :=
  not_isFFModule_image_of_marked_normal_range ρ i action f hf b normalizer_not_ff

/-- For a faithful local actor no passage to its image is needed. -/
theorem not_ff_of_marked_normal_range
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (f : K →* G) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (action.comp f)) : ¬ IsFFModule ρ :=
  not_isFFModule_of_marked_normal_range ρ hρ i action f hf b normalizer_not_ff

end ClassicalOrthogonal.FourPlusMatrix.Binary
