module

public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.SubrepresentationLattice

/-!
# The actual Chapter K hypotheses for the M₁₂ branch

The acting group is the finite SQTK group G, with the full known-simple
catalogue. Its generalized Fitting subgroup acts irreducibly on the faithful
binary module, and the cubic ratio is computed for G itself. The M₁₂ central
quotient marking is a separate explicit argument of the source theorems.
No degree bound or module-recognition conclusion is included in this input.

Source: Aschbacher--Smith, Chapter K introduction, printed p.451, and K.4,
printed pp.457--460 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
open Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The shared source hypotheses, before selecting the actual M₁₂ quotient. -/
structure Hypotheses {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)
  cubic_ratio : cubicRatio ρ ≤ 2

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
