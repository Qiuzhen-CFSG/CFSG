module

public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Representation.MathieuCodeRestriction
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Source hypotheses for the large Mathieu recognition branches

The actor is the actual finite SQTK group G for the full known-simple
catalogue; F*(G) is quasisimple and acts irreducibly on the faithful binary
module. The bound concerns the cubic ratio of this action of G.

The two degree assertions below are unproved input contracts for the
GM02 degree reduction, not assertions of a classification. Native small
module recognition is a separate input. The assembly in `Large` retains
both dual possibilities and the actual intertwining maps.

Source: Aschbacher–Smith, Chapter K, printed pp.451 and 457; Guralnick–Malle,
*Classification of 2F-modules, I*, Theorem 6.6 and Table 6.7,
DOI 10.1016/S0021-8693(02)00526-4.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
open Theory.GroupTheory Representation Representation.BinaryOffender Sporadic.Mathieu
universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The common Chapter K assumptions, with no classification conclusion. -/
structure SourceHypotheses (ρ : Representation (ZMod 2) G V) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)
  cubic_le_two : cubicRatio ρ ≤ 2

/-- The degree part of GM02 needed for the M₂₃ branch; it still includes covers. -/
def M23DegreeEleven : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
    SourceHypotheses ρ →
    Nonempty (generalizedFitting G ⧸ Subgroup.center (generalizedFitting G) ≃* M23) →
    Module.finrank (ZMod 2) V = 11

/-- The degree part of GM02 needed for the M₂₄ branch; it still includes covers. -/
def M24DegreeEleven : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
    SourceHypotheses ρ →
    Nonempty (generalizedFitting G ⧸ Subgroup.center (generalizedFitting G) ≃* M24) →
    Module.finrank (ZMod 2) V = 11

/-- Native degree-eleven completeness, with actual code/cocode equivariance. -/
def M23SmallRecognition : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V),
    Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 11 →
    MathieuCode.IsM23Code ρ ∨ MathieuCode.IsM23Cocode ρ

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
