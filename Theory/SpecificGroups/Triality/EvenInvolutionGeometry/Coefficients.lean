module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction

/-!
# Detection of cubic coefficient automorphisms on a triality root

A coefficient automorphism sends the actual short-root element with parameter
t to that with parameter e(t). The folded parameters are (t,F(t),F²(t)), and
e commutes with F. Faithfulness of the root parametrization after the central
quotient therefore detects every coefficient automorphism, including the cubic
order-three action at q = 2. In particular a coefficient action fixing the
positive subgroup pointwise is trivial. Mixed inner–coefficient actions require
a further Borel calculation; no such exclusion is assumed here.

Source: the pinned root actions of GLS3 §§2.4–2.5, used for the triality case
of Aschbacher–Smith 16.1.6 (`refs/quasithin.pdf`, printed p.1172).
-/

public section
noncomputable section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics OuterOdd
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

theorem coefficientAction_shortRoot (e : CoefficientAut P) (t : ExtensionField P) :
    coefficientAction P e (shortRoot n hn t) = shortRoot n hn (e t) := by
  change toCarrier P (coefficientElementary P e
    (sl2ElementaryLift P rfl (shortRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)))) =
    toCarrier P (sl2ElementaryLift P rfl (shortRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd (e t))))
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  change coefficientSplit P e
    (shortRankOneFixed n hn (Matrix.SpecialLinearGroup.upperUnipotentHom _
      (Multiplicative.ofAdd t))) =
    (shortRankOneFixed n hn (Matrix.SpecialLinearGroup.upperUnipotentHom _
      (Multiplicative.ofAdd (e t))) : SplitGroup P)
  refine (congrArg (coefficientSplit P e) (shortRankOneFixed_upper_val n hn t)).trans
    ((Eq.trans ?_ (shortRankOneFixed_upper_val n hn (e t)).symm))
  simp only [map_mul, positiveRoot, coefficientSplit_positive,
    fieldFrobenius_apply, map_pow]

/-- A coefficient automorphism fixing the actual folded root curve is identity. -/
theorem coefficient_eq_one_of_fixes_shortRoot (e : CoefficientAut P)
    (h : ∀ t : ExtensionField P, coefficientAction P e (shortRoot n hn t) =
      shortRoot n hn t) : e = 1 := by
  ext t
  exact shortRoot_injective n hn ((coefficientAction_shortRoot n hn e t).symm.trans (h t))

/-- The coefficient action on the genuine elementary central quotient is faithful. -/
theorem coefficientAction_injective : Function.Injective (coefficientAction P) := by
  intro e f h
  ext t
  apply shortRoot_injective n hn
  exact (coefficientAction_shortRoot n hn e t).symm.trans
    ((congrArg (fun a : MulAut (BinaryCarrier n hn) => a (shortRoot n hn t)) h).trans
      (coefficientAction_shortRoot n hn f t))

/-- No nontrivial pure coefficient action fixes the positive subgroup pointwise. -/
theorem coefficient_eq_one_of_fixes_unipotent (e : CoefficientAut P)
    (h : ∀ x ∈ unipotent P, coefficientAction P e x = x) : e = 1 :=
  coefficient_eq_one_of_fixes_shortRoot n hn e fun t =>
    h _ (shortRoot_mem_unipotent n hn t)

end Triality.Standard.EvenInvolutionGeometry
