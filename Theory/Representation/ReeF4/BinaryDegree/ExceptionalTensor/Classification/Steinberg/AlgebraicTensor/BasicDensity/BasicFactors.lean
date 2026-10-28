module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives

/-!
# Short-root density for exceptional basic F₄ factors

The first coefficients of the actual short-root actions generate the full
endomorphism algebra of every exceptional basic factor in characteristic two.
The basic highest weight has zero coefficients on the long simple roots and
coefficients zero or one on the short simple roots.

For a nonzero basic weight, negative short-root monomials span from a highest
vector. The positive short-root operators have a unique primitive line and
uniformly annihilate all sufficiently long words. Consequently every nonzero
short-root invariant subspace contains the highest vector and is the whole
space. Jacobson density over the algebraically closed field gives the claimed
algebra equality. Highest-weight uniqueness handles weight zero by comparison
with the one-dimensional trivial factor.

All spanning, primitive-line, and nilpotence premises are discharged here.
The remaining inputs are universality and the raw highest-weight uniqueness
contract; no reverse weight-uniqueness contract is needed. `RootExpansion`
links the coefficients throughout to the literal algebraic root actions.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and proof 11.1(1), pp. 52–53,
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The short-root ideal acts irreducibly on a factor with nonzero basic
highest weight. Negative cyclicity and the positive primitive line are proved
from the actual rational action, rather than assumed. -/
theorem RootExpansion.shortRootInvariant_eq_bot_or_top_of_nonzero_basic_highestWeight
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action)
    {b : BasicWeight} (hb : b ≠ (0, 0))
    (hB : Classification.HasBasicHighestWeight B b)
    (W : Submodule F B.Space)
    (hW : ∀ (r : F4Chevalley.Root), ¬ IsLongRoot r →
      ∀ w ∈ W, p.coeff r 1 w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨v, hv⟩ := hB
  have hspan := p.shortNegativeSpan_eq_top_of_basic_highestWeight hU hhigh hb hv
  obtain ⟨hkernel, hnil⟩ := p.positivePrimitives_of_negative_span hhigh hb hv hspan
  exact p.shortRootInvariant_eq_bot_or_top_of_highest_line v hspan hkernel hnil W hW

/-- The genuine first-degree short-root coefficients generate the full
endomorphism algebra of every basic factor, including basic weight zero. -/
theorem RootExpansion.hasShortRootDensity_of_basic_highestWeight
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action)
    {b : BasicWeight} (hB : Classification.HasBasicHighestWeight B b) :
    p.HasShortRootDensity := by
  by_cases hb : b = (0, 0)
  · subst b
    exact p.hasShortRootDensity_of_zero_highestWeight hhigh hB
  · apply BasicDensity.adjoin_eq_top_of_irreducible
    intro W hW
    exact p.shortRootInvariant_eq_bot_or_top_of_nonzero_basic_highestWeight
      hU hhigh hb hB W (fun r hr => hW ⟨r, hr⟩)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
