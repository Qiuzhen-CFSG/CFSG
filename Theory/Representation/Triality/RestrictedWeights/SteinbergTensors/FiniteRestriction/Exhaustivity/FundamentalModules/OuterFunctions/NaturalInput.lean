module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.RegularFunctions
public import Theory.AlgebraicGroup.Representations.Matrix

/-!
# A normalized coefficient of a natural D4 highest vector

A nonzero vector in an actual rational action gives globally regular matrix
coefficients. Choose a linear functional taking value one on the vector.
Its coefficient is normalized at the identity and inherits the vector's
actual torus eigencharacter and positive-root fixed-vector equations.

`NaturalModule` specifies the remaining geometric construction: an
eight-dimensional rational action of the given group with a nonzero vector
of left weight `Pi.single 0 1`. It is an output interface, not an existence
assertion. In particular, an action on an unrelated concrete carrier does
not inhabit it without a compatible algebraic map from the given group.

Sources: GLS3, Definitions 1.14.3, 1.14.5 and Example 1.14.9(d);
Steinberg, (6.1) and §13, `refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A normalized globally regular matrix coefficient of an actual highest vector. -/
theorem regularFunction_exists_of_vector (S : Geometry K) {a : Weight}
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (v : V) (hv : v ≠ 0)
    (ht : ∀ t : S.torus.carrierVariety.Point,
      (rho.action (S.torus.includePoint t)).1 v =
        (S.leftWeightEmbedding a).pointCharacter t • v)
    (hu : ∀ r ∈ S.roots.positive,
      ∀ z : (S.roots.rootSubgroup r).carrierVariety.Point,
        (rho.action ((S.roots.rootSubgroup r).includePoint z)).1 v = v) :
    ∃ f : K.PolynomialFunction, IsLeftHighestWeightRegularFunction S a f := by
  obtain ⟨e, m, hm⟩ := hrho
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
  let f := rationalRepresentationLinearMatrixCoefficient rho e m l v
  have hf (g) : f g = l ((rho.action g).1 v) :=
    rationalRepresentationLinearMatrixCoefficient_apply rho e m hm l v g
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hf, map_one]
    exact hl
  · intro t x
    rw [hf, hf, map_mul]
    change l ((rho.action x).1 ((rho.action (S.torus.includePoint t)).1 v)) = _
    rw [ht, map_smul, map_smul, smul_eq_mul]
  · intro r hr z x
    rw [hf, hf, map_mul]
    change l ((rho.action x).1
      ((rho.action ((S.roots.rootSubgroup r).includePoint z)).1 v)) = _
    rw [hu r hr z]

/-- The natural-module construction still required on the supplied geometry.
Rationality includes an actual algebraic map into a general linear group. -/
structure NaturalModule (S : Geometry K) where
  action : RationalRepresentation K (Fin 8 → k)
  rational : IsRationalRepresentation action
  vector : Fin 8 → k
  vector_ne_zero : vector ≠ 0
  torus : ∀ t : S.torus.carrierVariety.Point,
    (action.action (S.torus.includePoint t)).1 vector =
      (S.leftWeightEmbedding (Pi.single 0 1)).pointCharacter t • vector
  positive_root : ∀ r ∈ S.roots.positive,
    ∀ z : (S.roots.rootSubgroup r).carrierVariety.Point,
      (action.action ((S.roots.rootSubgroup r).includePoint z)).1 vector = vector

/-- An actual natural module supplies the first outer regular function.
Existence of the module remains a separate geometric obligation. -/
theorem NaturalModule.regularFunction_exists {S : Geometry K} (N : NaturalModule S) :
    ∃ f : K.PolynomialFunction,
      IsLeftHighestWeightRegularFunction S (Pi.single 0 1) f :=
  regularFunction_exists_of_vector S N.action N.rational N.vector N.vector_ne_zero
    N.torus N.positive_root

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
