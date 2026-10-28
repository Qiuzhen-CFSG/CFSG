module

public import Theory.FieldTheory.RationalFunctionSingletonPoleParameter
public import Theory.FieldTheory.RationalFunctionThreePoleTranslateFiniteness
public import Theory.FieldTheory.RationalFunctionTwoPoleTranslateFiniteness

/-!
# Infinitely many affine translates force a one-place parameter

Let `t : k(X)` be transcendental over an algebraically closed field.  This
module proves that if infinitely many constants `c : k` occur in identities
`sigma t = t + c`, for `k`-automorphisms `sigma` of `k(X)`, then some
transcendental generator `s` of `k(X)` makes `t` a polynomial in `s`.

This is the rational-function core of the completion argument in Borel,
*Linear Algebraic Groups*, Theorem 10.9
(`refs/KGroup/Bor1/Chapter3.tex`).  The lower field-theory modules imported
above formalize its precise reductions.  Automorphisms of `k(X)` are Mobius
transformations by the finrank/degree calculation in
`RationalFunctionMobius`; homogenized reduced denominators define a finite,
translation-invariant projective pole support, covariant under those
transformations, in `RationalFunctionProjectivePoles`.

The final argument is a cardinality split on that support.  Three or more
poles give only finitely many transformations by three-point projective
rigidity.  Exactly two poles give only finitely many translation parameters
after conjugating to `{0, infinity}` and comparing Laurent coefficients under
scaling and inversion.  Transcendence rules out empty support, so infinitude
forces exactly one pole.  The singleton-pole theorem sends it to infinity,
where the denominator is constant, and returns a transcendental coordinate
which generates `k(X)` and in whose polynomial algebra `t` lies.  No
algebraic-group or affine-line classification is used at this layer.
-/

universe u

open IntermediateField Polynomial

namespace RatFunc

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

/-- Infinitely many constant translates in the automorphism orbit of a
transcendental rational function force a one-place polynomial parameter. -/
public theorem infinite_affine_translates_exists_one_place_parameter_core
    (t : RatFunc k) (ht : Transcendental k t)
    (hinfinite : Set.Infinite {c : k | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
      sigma t = t + algebraMap k (RatFunc k) c}) :
    ∃ s : RatFunc k, Transcendental k s ∧
      IntermediateField.adjoin k {s} = ⊤ ∧ t ∈ Algebra.adjoin k {s} := by
  have hnotconst : ¬ ∃ c : k, t = C c := by
    rintro ⟨c, rfl⟩
    apply ht
    change IsAlgebraic k ((algebraMap k (RatFunc k)) c)
    exact isAlgebraic_algebraMap c
  have hsupportFinite := projectivePoleSupport_finite t
  have hsupportNonempty := projectivePoleSupport_nonempty hnotconst
  have hsupportPositive : 0 < t.projectivePoleSupport.ncard :=
    (Set.ncard_pos hsupportFinite).2 hsupportNonempty
  by_cases hthree : 3 ≤ t.projectivePoleSupport.ncard
  · exact (hinfinite
      (finite_affine_translate_parameters_of_three_le_ncard t hthree)).elim
  by_cases htwo : t.projectivePoleSupport.ncard = 2
  · exact (hinfinite
      (finite_affine_translate_parameters_of_projectivePoleSupport_ncard_eq_two t htwo)).elim
  have hone : t.projectivePoleSupport.ncard = 1 := by omega
  exact exists_one_place_parameter_of_projectivePoleSupport_ncard_eq_one t ht hone

end


end RatFunc
