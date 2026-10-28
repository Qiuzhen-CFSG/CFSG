module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterK.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Representation.Mathieu.M22James

/-!
# Source inputs and concrete outputs for the M₂₂ branch of Chapter K

The input retains the actual SQTK actor, its generalized Fitting subgroup,
its faithful binary action, irreducibility on that subgroup, the cubic ratio,
and an isomorphism of its actual central quotient with M₂₂. The output names
literal code, cocode and triple-cover actions through group and representation
isomorphisms. These definitions assert neither the degree bound nor recognition
nor an outer-action classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Chapter K,
printed pp.451 and 457; Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1 and Theorem 6.6/Table 6.7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
open Theory.GroupTheory Subgroup Representation
open _root_.Sporadic.Mathieu

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The genuine hypotheses of the M₂₂ source branch, without recognition data. -/
structure SourceHypotheses (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  component : L = generalizedFitting G
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp L.subtype)
  cubic : Representation.BinaryOffender.cubicRatio ρ ≤ 2
  quotient : Nonempty ((L ⧸ center L) ≃* M22)

/-- Recognition of the component action, allowing its actual group marking.
Permissible extensions of this action to G are an additional assertion. -/
def ComponentModels {L : Type*} [Group L] (σ : Representation (ZMod 2) L V) : Prop :=
  Representation.MathieuSmall.IsM22ToddOrDual σ ∨
    ∃ e : L ≃* M22TripleCover,
      Nonempty (Representation.Equiv σ (M22TripleCover.representationOfEquiv e))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
