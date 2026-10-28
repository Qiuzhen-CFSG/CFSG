module

public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Basic
public import Theory.AlgebraicGroup.RootData.StandardParabolicGenerated
public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
Source-level data for relative-root representation layers.

This module contains only the source-side wrapper around `RelativeRootSeries`
and the representation-source record used by the GLS3 relative-root
construction.  It deliberately sits below the standard parabolic relative-root
theorems: the data are phrased directly in terms of a root-group datum,
Chevalley parametrizations, a finite root family, and the chosen Levi closure.
Each chosen Chevalley coordinate is also certified by an algebraic-group
isomorphism from the additive group onto the corresponding root subgroup.  Its
included values agree with the chosen pointwise coordinate, providing the
geometric input needed to transport regular maps without admitting inseparable
Frobenius reparametrizations.

Keeping this interface separate lets later modules prove structural facts about
the source layers, such as closedness and normality, without importing the
heavier standard-parabolic setup or the unresolved representation theorems.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def sourceRelativeRootLayer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (base : Finset D.Root) (coeff : D.Root → D.Root → ℤ)
    (J : Set D.Root) (i : ℕ) : Subgroup (Variety.Point K) :=
  RelativeRootSeries D (Equiv.refl D.Root) base coeff J i

public structure RelativeRootRepresentationSource
    (K : Variety k) [AlgebraicGroup K] where
  isSimple : IsSimpleAlgebraicGroup K
  T : ClosedSubgroup K
  B : ClosedSubgroup K
  D : RootGroupData K T
  [finiteRoot : Finite D.Root]
  isRealization : D.IsRealization
  C : ChevalleyData K D
  X : Type u
  Y : Type u
  [addCommGroupX : AddCommGroup X]
  [moduleX : Module ℚ X]
  [addCommGroupY : AddCommGroup Y]
  [moduleY : Module ℚ Y]
  pairing : RootPairing D.Root ℚ X Y
  [isRootSystem : pairing.IsRootSystem]
  [isCrystallographic : pairing.IsCrystallographic]
  [isReduced : pairing.IsReduced]
  base : pairing.Base
  rootSystemRealization : IsRootSystemRealization D pairing (Equiv.refl D.Root) base
  chevalleySystem : IsChevalleySystem D C pairing (Equiv.refl D.Root) base
  chevalleyParametrization : (α : D.Root) →
    OneParameterParametrization (D.rootSubgroup α).carrierVariety
  chevalleyParametrization_value : ∀ α t,
    (D.rootSubgroup α).includePoint ((chevalleyParametrization α).value t) = C.x α t
  chevalleyTorus_mem : ∀ α t, C.h α t ∈ T
  classification : RootClassification
  dynkinType : HasDynkinType pairing classification
  coeff : D.Root → D.Root → ℤ
  simpleRootExpansion : HasSimpleRootExpansion pairing base coeff
  positiveRoots : Set D.Root
  positiveRoots_actual : positiveRoots = D.positive
  borel_alignment : B.toSubgroup = RootSubgroupGenerated D positiveRoots ⊔ T.toSubgroup
  J : Set D.Root
  J_simple : J ⊆ D.simple
  L : ClosedSubgroup K
  levi_alignment :
    L = subgroupZariskiClosure K
      (Subgroup.closure ((T : Set (Variety.Point K)) ∪
        standardLeviRootFactor D (RootSubsystemSpan D J)))
  torus_le_levi : T ≤ L
  height : ℕ
  height_pos : 0 < height
  root : D.Root
  root_height :
    RelativeRootHeight coeff D.simple.toFinite.toFinset J root = height

attribute [instance] RelativeRootRepresentationSource.finiteRoot
  RelativeRootRepresentationSource.addCommGroupX
  RelativeRootRepresentationSource.moduleX
  RelativeRootRepresentationSource.addCommGroupY
  RelativeRootRepresentationSource.moduleY
  RelativeRootRepresentationSource.isRootSystem
  RelativeRootRepresentationSource.isCrystallographic
  RelativeRootRepresentationSource.isReduced

end Theory.AlgebraicGroup
