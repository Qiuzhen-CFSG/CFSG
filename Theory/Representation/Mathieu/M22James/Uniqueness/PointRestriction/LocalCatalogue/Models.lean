module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.CentralReduction

/-!
# Concrete six-dimensional binary candidates for SL₃(4)

The two labels mean the actual natural and inverse-transpose actions, on
three coordinates over F₄. Both are faithful binary modules of dimension
six satisfying the central quadratic relation. Their pairwise direct sums
are actual twelve-dimensional candidates. Completeness and nonsplit
extensions are separate obligations of the local catalogue.

Source context: James (1973), Lemma 8.3, and Aschbacher–Smith H.12.1,
printed pp.393–394. No Mathieu subgroup identification is used here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Representation.SL3FourLocalCatalogue

abbrev W := SL3FourNaturalDual.W

/-- The two concrete candidate constituent actions; this label asserts no completeness. -/
inductive Constituent
  | natural | dual
  deriving DecidableEq, Fintype

/-- The binary action of a candidate constituent on its concrete carrier. -/
def constituent : Constituent → Representation (ZMod 2) SL W
  | .natural => SL3FourNaturalDual.natural
  | .dual => SL3FourNaturalDual.dualCoordinates

lemma constituent_finrank : Module.finrank (ZMod 2) W = 6 :=
  SL3FourNaturalDual.finrank_natural

lemma central_inverseTranspose : Matrix.SpecialLinearGroup.inverseTranspose z = z ^ 2 := by
  have hi : z⁻¹ = z ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    decide +kernel
  change (z⁻¹).transpose = z ^ 2
  rw [hi]
  apply Subtype.ext
  change ((Matrix.diagonal (fun _ : Fin 3 => SL3FourNaturalDual.omega)) ^ 2).transpose =
    (Matrix.diagonal (fun _ : Fin 3 => SL3FourNaturalDual.omega)) ^ 2
  rw [Matrix.transpose_pow, Matrix.diagonal_transpose]

lemma constituent_centralQuadratic (a : Constituent) : CentralQuadratic (constituent a) := by
  cases a with
  | natural =>
    apply LinearMap.ext
    exact SL3FourNaturalDual.centralScalar_norm
  | dual =>
    apply LinearMap.ext
    intro v
    change SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose z)
      (SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose z) v) +
      SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose z) v + v = 0
    rw [central_inverseTranspose]
    have hs (w : W) : SL3FourNaturalDual.natural (z ^ 2) w =
        (SL3FourNaturalDual.omega * SL3FourNaturalDual.omega) • w := by
      rw [SL3FourNaturalDual.natural.map_pow]
      change SL3FourNaturalDual.natural z (SL3FourNaturalDual.natural z w) = _
      rw [SL3FourNaturalDual.centralScalar_natural,
        SL3FourNaturalDual.centralScalar_natural, smul_smul]
    simp only [hs, smul_smul]
    calc
      _ = ((SL3FourNaturalDual.omega * SL3FourNaturalDual.omega) *
        (SL3FourNaturalDual.omega * SL3FourNaturalDual.omega) +
        SL3FourNaturalDual.omega * SL3FourNaturalDual.omega + 1) • v := by
          rw [add_smul, add_smul, one_smul]
      _ = 0 := by rw [show (SL3FourNaturalDual.omega * SL3FourNaturalDual.omega) *
        (SL3FourNaturalDual.omega * SL3FourNaturalDual.omega) +
        SL3FourNaturalDual.omega * SL3FourNaturalDual.omega + 1 = 0 by decide +kernel,
        zero_smul]

lemma constituent_faithful (a : Constituent) : Function.Injective (constituent a) := by
  have hn : Function.Injective SL3FourNaturalDual.natural := by
    intro g h he
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun he v
  cases a with
  | natural => exact hn
  | dual =>
    intro g h he
    change SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose g) =
      SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose h) at he
    have hh := hn he
    have hhh := congrArg Matrix.SpecialLinearGroup.inverseTranspose hh
    simpa only [SL3FourNaturalDual.inverseTranspose_involutive] using hhh

/-- All four ordered split candidates on the actual product carrier. -/
def splitRepresentation (a b : Constituent) : Representation (ZMod 2) SL (W × W) :=
  (constituent a).prod (constituent b)

lemma split_finrank : Module.finrank (ZMod 2) (W × W) = 12 :=
  SL3FourNaturalDual.finrank_space

lemma split_centralQuadratic (a b : Constituent) :
    CentralQuadratic (splitRepresentation a b) := by
  apply LinearMap.ext
  intro v
  exact Prod.ext
    (centralQuadratic_apply _ (constituent_centralQuadratic a) v.1)
    (centralQuadratic_apply _ (constituent_centralQuadratic b) v.2)

lemma split_faithful (a b : Constituent) : Function.Injective (splitRepresentation a b) := by
  intro g h he
  apply constituent_faithful a
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v, 0))

end Representation.SL3FourLocalCatalogue
