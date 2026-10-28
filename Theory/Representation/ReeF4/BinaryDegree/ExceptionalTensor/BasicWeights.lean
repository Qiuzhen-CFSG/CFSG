module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.AlgebraicFactors

/-!
# The exceptional basic highest weights of F4 in characteristic two

The fixed standard simple roots are numbered `0,1,2,3`; the first two are
geometrically long and the last two short. An exceptional basic weight has
coefficients zero on the long roots and coefficients zero or one on the
short roots. We express this using a nonzero vector fixed by every positive
root group and the eigenvalues of actual simple-coroot elements.

The coroot convention here is `n_alpha(t) * n_alpha(1)⁻¹`, which gives
`diag(t,t⁻¹)` in the usual rank-one coordinates. This is the inverse of the
`rootHElement` convention in `IntegralChevalleyRootCurves`. The explicit
choice ensures that the dominant highest-weight coefficients below are
nonnegative.

These are definitions of genuine actions and weights. In particular,
`BasicFactorMinimum` does not assert that its bound has been proved.

Source: GLS3, Definition 2.8.1(b) and Remark 2.8.4; its F4 diagram and simple
root numbering appear in Chapter 1, §1.8. See also
`typeF4CorootScale_simpleRoot` for the long/short convention.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The concrete algebraic root element in the closed F4 carrier. -/
@[expose] noncomputable def algebraicRootElement (r : F4Chevalley.Root) (t : F) :
    Variety.Point (F4Chevalley.Carrier (k := F)) :=
  (F4Chevalley.rootMorphism r).onPoints (kPlusPoint t)

/-- The standard rank-one normalizer word formed inside the actual carrier. -/
@[expose] noncomputable def algebraicNElement (r : F4Chevalley.Root) (t : Fˣ) :
    Variety.Point (F4Chevalley.Carrier (k := F)) := by
  letI := typeF4RootPairing.indexNeg
  exact algebraicRootElement r (t : F) *
    algebraicRootElement (-r) (-((t : F)⁻¹)) * algebraicRootElement r (t : F)

/-- Positive-coroot convention, acting as `diag(t,t⁻¹)` in rank one. -/
@[expose] noncomputable def algebraicCorootElement (r : F4Chevalley.Root) (t : Fˣ) :
    Variety.Point (F4Chevalley.Carrier (k := F)) :=
  algebraicNElement r t * (algebraicNElement r (1 : Fˣ))⁻¹

/-- The two short-simple coefficients, with the long-simple coefficients zero. -/
@[expose] def basicCoefficient (weight : Fin 2 × Fin 2) (i : Fin 4) : ℕ :=
  if i = 2 then weight.1.val else if i = 3 then weight.2.val else 0

/-- Source exceptional basicness, specified by a highest-weight vector for
the actual positive root groups and simple coroots. -/
@[expose] def AlgebraicFactor.IsExceptionalBasic (B : AlgebraicFactor F) : Prop :=
  ∃ (weight : Fin 2 × Fin 2) (v : B.Space), v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v =
        ((t : F) ^ basicCoefficient weight i) • v)

/-- The minimum needed only for the nontrivial exceptional basic factors. -/
@[expose] def BasicFactorMinimum (F : Type u) [Field F] [IsAlgClosed F]
    (b : ℕ) : Prop :=
  ∀ B : AlgebraicFactor F, B.IsExceptionalBasic → B.IsNontrivial →
    b ≤ Module.finrank F B.Space

end ReeF4.BinaryDegree.ExceptionalTensor
