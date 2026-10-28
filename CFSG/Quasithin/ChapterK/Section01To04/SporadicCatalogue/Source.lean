module

public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Source hypotheses and remaining sporadic exclusion contracts

These are the actual hypotheses in the opening of Chapter K, printed p.451.
The component is literally F*(G); the K-group parameter is the full known-simple
catalogue. Small cubic ratio concerns the ambient action, whose restriction to
that component is irreducible. No recognition or exclusion is a field.

The bounded contracts isolate the remaining representation calculations after
the degree reduction. They are definitions of obligations, not assertions that
the exclusions hold. The final K.4 assembly must discharge every such input.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open scoped ENNReal
universe u v

/-- Chapter K's literal ambient hypotheses, with no family recognition built in. -/
structure SourceHypotheses {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)
  cubic_le_two : cubicRatio ρ ≤ 2

/-- Exclusion of one specified central quotient under the full source hypotheses. -/
def SourceExclusion (name : KnownSimple.SporadicName) : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), SourceHypotheses ρ →
    Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃* name.Carrier) →
    False

/-- The remaining calculation within a proved degree window. It retains the
source SQTK, cubic, covering and outer-action hypotheses. -/
def BoundedSourceExclusion (name : KnownSimple.SporadicName) (d : ℕ) : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), SourceHypotheses ρ →
    Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃* name.Carrier) →
    Module.finrank (ZMod 2) V ≤ d → False

end CFSG.Quasithin.ChapterK.SporadicCatalogue
