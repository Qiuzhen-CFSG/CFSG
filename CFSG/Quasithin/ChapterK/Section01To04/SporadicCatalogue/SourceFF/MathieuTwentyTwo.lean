module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuCode
public import Theory.Representation.Mathieu.M22James.NoFF

/-!
# The original M22 source action has no FF offenders

The source classification marks the full original action as code, cocode, or
the genuine triple-cover action. The first two cases are already excluded;
the checked Hermitian pointwise-fixer calculation excludes the last one.
The actual injective actor map and full-action intertwiner transport its
exclusion, including all permitted outer actors and the nontrivial odd center.

Source: Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457--459; H.12.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Representation Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The literal triple action excludes FF after the source's actual full-action marking. -/
theorem not_ff_of_marked_m22Triple (D : M22Source.MarkedTripleModel ρ L) :
    ¬ IsFFModule ρ :=
  _root_.Sporadic.Mathieu.M22TripleCover.NoFF.markedAction_not_isFFModule
    ρ D.embedding D.injective D.equivalence

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- No additional degree, recognition, or local-geometry premise remains in the M22 branch. -/
theorem not_ff_m22 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier)) :
    ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨D⟩ := m22_triple_of_ff h hff he
  exact not_ff_of_marked_m22Triple D hff
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
