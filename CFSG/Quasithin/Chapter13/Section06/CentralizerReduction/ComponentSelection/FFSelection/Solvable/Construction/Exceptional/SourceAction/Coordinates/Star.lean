module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action

/-!
# Ambient coordinates on the literal star offender representation

The native FF hypothesis is supplied by the original star quotient map and
SQTK cover. Applying the coordinate construction to the explicit recovered
data preserves U_v, both original outer factors, and both moved actions.
The source-action owner supplies `Recovered` from the earlier source inputs.

Source: Aschbacher–Smith, B.5.7, p.106; 13.6.13, p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
universe u v

private theorem coordinates_native_offender_hypothesis {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    {C : Type u} [Group C] [Finite C] {K : GroupClass.{u}}
    (f : C →* D) (hf : Function.Surjective f) (hC : IsSQTK K C)
    (hfaith : Function.Injective σ) (hcore : pCore 2 D = ⊥) :
    ChapterB.SourceInduction.FFHypothesis K (FFFactors.offenderRepresentation σ) := by
  have h := FFFactors.offender_hypothesis σ f hf hC hfaith hcore
  refine ⟨h.finite_module, h.faithful, h.twoCore, h.generated, ?_⟩
  obtain ⟨d⟩ := h.quotient
  let := d.coverGroup
  let := d.coverFinite
  let := d.kernelNormal
  exact ⟨{ Cover := d.Cover, kernel := d.kernel, sqtk := d.sqtk, equiv := d.equiv }⟩

/-- Simultaneous ambient coordinates for the literal offender restriction
of the star action; the recovered source data remains explicit. -/
theorem coordinates_star_offender {G : Type u} [Group G] [Finite G]
    (z v : G) [IsElementaryAbelian 2 (Uv z v)] {K : GroupClass.{u}}
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v)))
    (d : Recovered c (FFFactors.offenderRepresentation (starRepresentation z v))) :
    Nonempty (AmbientCoordinates c (FFFactors.offenderRepresentation (starRepresentation z v))) := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  exact coordinates c (FFFactors.offenderRepresentation (starRepresentation z v))
    (coordinates_native_offender_hypothesis (starRepresentation z v) (starMk z v)
      (starMk_surjective z v) hlocal (starRepresentation_injective z v) hcore) d

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
