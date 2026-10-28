module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteGeometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.HighestRoot
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.LeftAssembly
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Cells
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Reflections
/-!
# Actual basic highest-weight modules for the Clifford Spin group

The identity comparison with the concrete Spin pinning supplies the three outer
fundamental modules. Positive roots centralize the actual highest root, supplying
the fourth fundamental module through the adjoint action. Tensor products and
irreducible sections then construct every nonnegative highest weight, including
all sixteen binary basic weights. The actual simple normalizers give the 8/24
degree bounds. Complementary sections use these same left highest weights.

Universality of the Spin algebraic group is the sole remaining geometric input;
no module existence or representation classification is assumed. This is the
basic-family producer for the finite restricted triality tensor argument, not
an assertion of finite irreducibility or an involution displacement bound.
Source: GLS3 §§1.14 and 2.8; Steinberg §§12–13.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors
open FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
@[expose] public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem rawTorusCoordinates_parameter (t : Fin 4 → kˣ) :
    OuterFunctions.rawTorusCoordinates k (finiteGeometry k hu)
      (CorootTorus.parameterPoint k t) = t := by
  funext i
  apply Units.ext
  change (weightEquiv k (Multiplicative.ofAdd (Pi.single i 1))).pointCharacter
    (CorootTorus.parameterPoint k t) = (t i : k)
  rw [weightEquiv_apply]
  rw [CorootTorus.weightEmbedding_parameter]
  classical
  simp [Pi.single_apply]

def spinComparison : OuterFunctions.SpinComparison k (finiteGeometry k hu) where
  morphism := Morphism.id _
  torus := by
    intro t
    obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
    change (CorootTorus.closedSubgroup k).includePoint
      ((CorootTorus.coordinateIso k).hom.onPoints x) =
      CorootTorus.parameter k (OuterFunctions.rawTorusCoordinates k (finiteGeometry k hu)
        ((CorootTorus.coordinateIso k).hom.onPoints x))
    rw [CorootTorus.coordinateIso_hom_apply, rawTorusCoordinates_parameter]
    exact CorootTorus.inclusion_parameterPoint k _
  positive_root := by
    intro r hr z
    let :=  ((pinnedRootData k).rootSubgroup r).carrierAlgebraicGroup
    obtain ⟨a, rfl⟩ := (pinnedRootParametrization k r).toMulEquiv.surjective z
    obtain ⟨b, rfl⟩ := (additiveGroupPointEquiv k).symm.surjective a
    exact ⟨b.toAdd, pinnedRootParametrization_inclusion k r b.toAdd⟩

def naturalModule : OuterFunctions.NaturalModule (finiteGeometry k hu) :=
  OuterFunctions.naturalModule_of_spinComparison k _ (spinComparison k hu)

theorem positiveCentralizesHighestRoot :
    FundamentalModules.PositiveCentralizesHighestRoot (finiteGeometry k hu) := by
  intro r hr x hx y hy
  obtain ⟨a, rfl⟩ := (mem_rootClosedSubgroup_iff k r.down x).mp hx
  obtain ⟨b, rfl⟩ := (mem_rootClosedSubgroup_iff k
    FundamentalModules.highestRootIndex y).mp hy
  exact positive_rootPoint_commute_highest k r.down hr a b

theorem fundamentalExistence : LeftFundamentalRationalExistence (finiteGeometry k hu) :=
  leftFundamentalRationalExistence_of_centralizes_of_outerRegularFunctions _
    (positiveCentralizesHighestRoot k hu)
    (leftOuterRegularFunction_exists_of_naturalModule _ (naturalModule k hu))

theorem rationalFactor_exists (a : Weight) (ha : ∀ i, 0 ≤ a i) :
    ∃ A : RationalFactor (groupVariety k), HasLeftHighestWeight (finiteGeometry k hu) A a :=
  leftRationalFactor_exists_of_nonnegative_of_fundamentals _ (fundamentalExistence k hu) a ha

theorem restrictedRationalExistence (n : ℕ) :
    LeftRestrictedRationalExistence (finiteGeometry k hu) n :=
  leftRestrictedRationalExistence_of_fundamentals _ (fundamentalExistence k hu) n

def basicFamily : RationalBasicFamily (finiteGeometry k hu).bigCell.data.B
    (finiteGeometry k hu).torus (finiteGeometry k hu).leftWeightEmbedding where
  factor a := Classical.choose (rationalFactor_exists k hu (coefficient a)
    (by intro i; dsimp [coefficient]; split_ifs <;> norm_num))
  highest a := Classical.choose_spec (rationalFactor_exists k hu (coefficient a)
    (by intro i; dsimp [coefficient]; split_ifs <;> norm_num))

theorem basic_finrank_lower_bounds (a : BasicWeight) (ha : a ≠ zeroWeight) :
    8 ≤ Module.finrank k ((basicFamily k hu).factor a).Space ∧
      (diagramAction a = a → 24 ≤ Module.finrank k ((basicFamily k hu).factor a).Space) := by
  let := (finiteGeometry k hu).torus.carrierAlgebraicGroup
  obtain ⟨v, hv⟩ := (basicFamily k hu).highest a
  have hraw (i : Fin 4) (z : Weight)
      (t : (finiteGeometry k hu).torus.carrierVariety.Point) :
      ((finiteGeometry k hu).coordinateEmbedding (reflection i z)).pointCharacter t =
      ((finiteGeometry k hu).coordinateEmbedding z).pointCharacter
        ((CorootTorus.torusReflection k i).onPoints t) := by
    change (weightEquiv k (Multiplicative.ofAdd (reflection i z))).pointCharacter t =
      (weightEquiv k (Multiplicative.ofAdd z)).pointCharacter _
    rw [weightEquiv_apply, weightEquiv_apply]
    exact CorootTorus.weightEmbedding_reflection k i z t
  have hweight : weightSpace ((basicFamily k hu).factor a).action
      (finiteGeometry k hu).torus
      ((finiteGeometry k hu).leftWeightEmbedding (coefficient a)) ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    exact ⟨v, hv.2.2, hv.1.1⟩
  exact left_basic_finrank_lower_bounds_of_conjugation (finiteGeometry k hu)
    ((basicFamily k hu).factor a).action (simpleNormalizer k)
    (fun i => (CorootTorus.torusReflection k i).onPoints)
    (CorootTorus.torusReflection_conjugation k) hraw a hweight ha

theorem complementarySections (n : ℕ) :
    LeftComplementarySections (finiteGeometry k hu) n :=
  leftComplementarySections_of_highestWeightExistence _ n (rationalFactor_exists k hu)

end
end Triality.RestrictedWeights.Concrete
