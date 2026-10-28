module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.CoordinatesContract
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Star
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action

/-!
# The B.5.7 actions on the original module and star offender representation

The source recovery constructs the marked symmetric supplement and cubic
plane. The supplement extends the six-point coordinates to the whole group;
the binary plane supplies the three-point coordinates. Their signs agree,
giving one isomorphism with the parity subgroup of S₆ × S₃ and both actual
linear intertwiners. `recover_action` retains these coordinates together
with the disjoint moved spaces and the odd fixed/moved complement.

The star application keeps the literal U_v, star quotient map, and offender
restriction. Both assemblies use only the complete earlier inputs listed in
`EarlierSources`: B.5.1 (`qt-b05-quasisimple`), B.5.2 and B.5.5
(`qt-b05-quotient-components`), A.2.1 (`qt-a-02`), and the full I.1.3 table
(`qt-i-01`, including `qt-i01-lie-a2`). There is no B.5.6/B.5.7 or recovered
module-witness premise. No splitting with the global fixed space is asserted.
The outer exclusion and its Sylow and L_v transports remain with the parent.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.7,
printed p.106, and 13.6.13, printed p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction

open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
universe u v

/-- The recovered source data and both ambient actions on the same original
module. The kernels in `ambient` mark the original factors of `c`. -/
structure RecoveredAction {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (c : ChapterB.OuterSixThreeShape D) (σ : Representation (ZMod 2) D W) where
  recovered : Recovered c σ
  ambient : AmbientCoordinates c σ

/-- Recover the genuine B.5.7 module information from the native FF
hypothesis and complete earlier sources. Both linear intertwiners use the
same constructed ambient actor equivalence; no module witness is assumed. -/
theorem recover_action {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (c : ChapterB.OuterSixThreeShape D) (σ : Representation (ZMod 2) D W)
    {K : GroupClass.{u}} (earlier : EarlierSources.{u,v} K)
    (hyp : ChapterB.SourceInduction.FFHypothesis K σ) :
    Nonempty (RecoveredAction c σ) := by
  obtain ⟨d⟩ := recover c σ earlier hyp
  obtain ⟨a⟩ := coordinates c σ hyp d
  exact ⟨⟨d, a⟩⟩

/-- The recovery target on the literal offender restriction of any action. -/
abbrev OffenderRecovered {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor σ)) :=
  Recovered (G := FFFactors.offenderActor σ) (V := W) c
    (FFFactors.offenderRepresentation σ)

private theorem native_offender_hypothesis {D : Type u} [Group D] [Finite D]
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

variable {G : Type u} [Group G] [Finite G]

/-- Recover B.5.7's local action data on the literal offender restriction
of the original star action. The SQTK cover and quotient map are those of
`starMk`; no replacement carrier or B.5.6 module witness is assumed. -/
theorem recover_star_offender (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    {K : GroupClass.{u}} (earlier : EarlierSources.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    Nonempty (OffenderRecovered (D := Gstar z v) (W := Additive (Uv z v))
      (starRepresentation z v) c) := by
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  exact recover c (FFFactors.offenderRepresentation (starRepresentation z v)) earlier
    (native_offender_hypothesis (starRepresentation z v) (starMk z v)
      (starMk_surjective z v) hlocal (starRepresentation_injective z v) hcore)

/-- The full recovered action on the literal offender restriction of the
original star representation. This discharges the coordinate construction's
`Recovered` premise with B.5.7's source recovery, retaining the original
quotient, factors, moved spaces, and valid supplement/decomposition clauses. -/
theorem recover_star_offender_action (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    {K : GroupClass.{u}} (earlier : EarlierSources.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : ChapterB.OuterSixThreeShape (FFFactors.offenderActor (starRepresentation z v))) :
    Nonempty (RecoveredAction c
      (FFFactors.offenderRepresentation (starRepresentation z v))) := by
  obtain ⟨d⟩ := recover_star_offender z v earlier hlocal hcore c
  obtain ⟨a⟩ := coordinates_star_offender z v hlocal hcore c d
  exact ⟨⟨d, a⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
