module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.Transport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleWords
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.RootTransport

/-!
# Assembly of charts for the literal F4 opposite-root pairs

A compatible regular SL₂ morphism supplies each simple-root chart, including
its source-convention diagonal containment. Conjugation by an actual point
preserving the split torus then transports the chart to a specified literal
opposite pair. The polynomial simple-root SL₂ morphisms and the integral Tits
transport discharge both inputs, giving charts for every literal root over
any algebraically closed field of characteristic two. Their cocharacters use
the GLS word `n(1)⁻¹n(t)`, whose SL₂ matrix is `diag(t⁻¹,t)`.

Source: GLS3, Theorem 1.9.5(c,d), Remarks 1.9.6, and the defining formulas of
Theorem 1.12.1 in `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Simple-root realizations and simultaneous torus/opposite-pair transport
supply charts for every literal root. Both construction inputs remain explicit. -/
theorem literalCharts_of_simpleMorphisms_of_transport
    (hmorph : ∀ i : typeF4RootPairing_base.support,
      ∃ f : Morphism (slVariety k 2) (Carrier (k := k)),
        f.comp standardSL2UpperMorphism = rootMorphism i ∧
        f.comp standardSL2LowerMorphism =
          rootMorphism (typeF4RootPairing.reflectionPerm i i))
    (htransport : ∀ r : Root,
      ∃ (i : typeF4RootPairing_base.support) (g : Variety.Point (Carrier (k := k))),
        (splitTorus (k := k)).conjugate g = splitTorus ∧
        (rootSubgroup (k := k) i).conjugate g = rootSubgroup r ∧
        (rootSubgroup (k := k) (typeF4RootPairing.reflectionPerm i i)).conjugate g =
          rootSubgroup (typeF4RootPairing.reflectionPerm r r))
    (r : Root) :
    Nonempty (BinaryOppositeRootSL2Chart (splitTorus (k := k)) (rootSubgroup r)
      (rootSubgroup (typeF4RootPairing.reflectionPerm r r))) := by
  obtain ⟨i, g, hT, hp, hm⟩ := htransport r
  obtain ⟨f, hfplus, hfminus⟩ := hmorph i
  have C := (simpleChart i f hfplus hfminus).conjugate g
  rw [hT, hp, hm] at C
  exact ⟨C⟩

/-- Every literal F4 opposite-root pair admits actual one-parameter
parametrizations and a compatible regular SL₂ map into its closed generated
subgroup, with the source-convention diagonal image in the literal split torus. -/
theorem literalRootSL2Charts (r : Root) :
    Nonempty (BinaryOppositeRootSL2Chart (splitTorus (k := k)) (rootSubgroup r)
      (rootSubgroup (typeF4RootPairing.reflectionPerm r r))) :=
  literalCharts_of_simpleMorphisms_of_transport
    simpleRootSL2Morphisms literalRootPairTransport r

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
