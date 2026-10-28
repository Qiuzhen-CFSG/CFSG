module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Data
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Root words for the D4 point comparison

The alphabet consists of the 24 numbered D4 roots with field parameters.
The displayed relations are root addition, the simply laced commutator
relations, and multiplicativity of the coroot words. In characteristic two
all Chevalley signs disappear. The inverse-conjugation coroot convention is
`h(t) = n(1)⁻¹ n(t)`.

`NormalizedParameters` asks for compatible parametrizations of the actual
root subgroups satisfying these relations and matching the four supplied
coroots. It does not assert existence or a presentation theorem. In particular,
the reverse kernel inclusion remains separate from evaluation of relators.

Source: GLS3 §§1.12--1.14, especially Theorems 1.12.1 and 1.12.4,
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
namespace SpinComparisonExistence.PointConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning

universe u
variable (k : Type u) [Field k]

/-- Words in the actual numbered D4 root alphabet. -/
abbrev RootWord := FreeGroup (RootIndex × k)

/-- A single root letter. -/
def x (r : RootIndex) (a : k) : RootWord k := FreeGroup.of (r, a)

/-- The formal normalizer word. -/
def n (r : RootIndex) (t : kˣ) : RootWord k :=
  x k r t * x k (negativeRoot r) (-((t : k)⁻¹)) * x k r t

/-- The raw coroot word, in the source order. -/
def h (r : RootIndex) (t : kˣ) : RootWord k := (n k r 1)⁻¹ * n k r t

/-- The source convention for a commutator. -/
def comm (r s : RootIndex) (a b : k) : RootWord k :=
  (x k r a)⁻¹ * (x k s b)⁻¹ * x k r a * x k s b

/-- Standard simply laced Steinberg relators, including the torus relations.
Opposite roots are excluded from the commutator clauses. -/
inductive Relator : RootWord k → Prop
  | addition (r : RootIndex) (a b : k) :
      Relator (x k r a * x k r b * (x k r (a + b))⁻¹)
  | sum (r s q : RootIndex) (hrs : r ≠ s) (hopp : r ≠ negativeRoot s)
      (hq : typeDRootVector 4 q = typeDRootVector 4 r + typeDRootVector 4 s)
      (a b : k) : Relator (comm k r s a b * (x k q (a * b))⁻¹)
  | noSum (r s : RootIndex) (hrs : r ≠ s) (hopp : r ≠ negativeRoot s)
      (hq : ∀ q, typeDRootVector 4 q ≠ typeDRootVector 4 r + typeDRootVector 4 s)
      (a b : k) : Relator (comm k r s a b)
  | torus (r : RootIndex) (t v : kˣ) :
      Relator (h k r t * h k r v * (h k r (t * v))⁻¹)

/-- The explicitly displayed relations, as a normal subgroup of root words. -/
def relationSubgroup : Subgroup (RootWord k) := Subgroup.normalClosure {w | Relator k w}

variable [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Freely choose algebraic parametrizations of the actual root groups. -/
abbrev ParameterFamily (S : Geometry K) :=
  ∀ r, OneParameterParametrization (S.roots.rootSubgroup r).carrierVariety

/-- Evaluation on actual root subgroup points, using the published numbering. -/
def sourceEvaluation (S : Geometry K) (p : ParameterFamily k S) : RootWord k →* K.Point :=
  FreeGroup.lift fun ra => (S.roots.rootSubgroup (S.rootIndex.symm ra.1)).includePoint
    ((p (S.rootIndex.symm ra.1)).value ra.2)

/-- Evaluation in the genuine Clifford Spin point group. -/
def spinEvaluation : RootWord k →* Points k :=
  FreeGroup.lift fun ra => rootPoint k ra.1 ra.2

omit [IsAlgClosed k] in
@[simp] theorem sourceEvaluation_x (S : Geometry K) (p : ParameterFamily k S)
    (r : S.roots.Root) (a : k) :
    sourceEvaluation k S p (x k (S.rootIndex r) a) =
      (S.roots.rootSubgroup r).includePoint ((p r).value a) := by
  simp only [sourceEvaluation, x, FreeGroup.lift_apply_of]
  rw [Equiv.symm_apply_apply]

@[simp] theorem spinEvaluation_x (r : RootIndex) (a : k) :
    spinEvaluation k (x k r a) = rootPoint k r a := by
  simp [spinEvaluation, x]

@[simp] theorem spinEvaluation_n (r : RootIndex) (t : kˣ) :
    spinEvaluation k (n k r t) = normalizerWord k r t := by
  simp [n, normalizerWord]

@[simp] theorem spinEvaluation_h (r : RootIndex) (t : kˣ) :
    spinEvaluation k (h k r t) = corootWord k r t := by
  simp [h, corootWord]

/-- A compatible source pinning. Its existence is a geometric obligation;
no homomorphism to Spin or kernel comparison is stored here. -/
structure NormalizedParameters (S : Geometry K) where
  parameter : ParameterFamily k S
  coroot : ∀ (i : Fin 4) (z : (KMult k).Point),
    sourceEvaluation k S parameter (h k (simpleRoot i) (dPointEquiv 1 z 0)) =
      S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)
  relations : ∀ w, Relator k w → sourceEvaluation k S parameter w = 1

omit [IsAlgClosed k] in
/-- The forward kernel inclusion is just evaluation of the displayed relations.
It does not prove that they present the source group. -/
theorem NormalizedParameters.relationSubgroup_le_ker (S : Geometry K)
    (p : NormalizedParameters k S) :
    relationSubgroup k ≤ (sourceEvaluation k S p.parameter).ker := by
  exact Subgroup.normalClosure_le_normal p.relations

end SpinComparisonExistence.PointConstruction
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
