module

public import Theory.GroupTheory.ThreeConjugateAutomorphisms.Inner
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Reducing J₄ conjugate generation to its two actual involution classes

The existing odd-index and local-fusion proofs cover all involutions of
`Janko4.Model` by the ATLAS words `a` and `(ababb)^5`. Full innerness and
triviality of the center then reduce involutory automorphism generation to
one generating triple for each of these two representatives.

The two triples remain explicit premises. The source generation theorem is
Revin–Zavarnitsine, https://arxiv.org/abs/2505.05173v2, Theorem 1; the concrete
carriers and words retain their ATLAS attribution in `GeneratorCertificates`.
This reduction does not assume a classification or a representation exclusion.
-/

public section
namespace Janko4.ThreeConjugates
open Subgroup Theory.GroupTheory
attribute [local irreducible] modelGroup matrixA matrixB

/-- The two literal ATLAS words cover every involution in the actual carrier. -/
theorem involution_classes {x : Model} (hx : orderOf x = 2) :
    IsConj a x ∨ IsConj ((a * b * a * b * b) ^ 5) x :=
  OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hx

/-- Only the two representative triples remain after the proved class coverage. -/
theorem involutions_of_representatives
    (hfirst : ThreeConjugatesGenerate a)
    (hsecond : ThreeConjugatesGenerate ((a * b * a * b * b) ^ 5))
    {x : Model} (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    ThreeConjugatesGenerate x := by
  obtain ha | hb := involution_classes (orderOf_eq_prime hx2 hx)
  · exact hfirst.of_isConj ha
  · exact hsecond.of_isConj hb

/-- This is the actual automorphism-generation contract, conditional on the
two concrete triples only. All class and innerness premises are discharged. -/
theorem automorphisms_of_representatives
    [IsSimpleGroup Model] [Group.IsPerfect Model]
    (hfirst : ThreeConjugatesGenerate a)
    (hsecond : ThreeConjugatesGenerate ((a * b * a * b * b) ^ 5)) :
    ThreeConjugateAutomorphisms Model := by
  apply threeConjugateAutomorphisms_of_inner
    (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect)
    (fun t _ => AdequateLocal.conj_surjective t)
  intro x hx
  obtain ha | hb := involution_classes hx
  · exact hfirst.of_isConj ha
  · exact hsecond.of_isConj hb

end Janko4.ThreeConjugates
