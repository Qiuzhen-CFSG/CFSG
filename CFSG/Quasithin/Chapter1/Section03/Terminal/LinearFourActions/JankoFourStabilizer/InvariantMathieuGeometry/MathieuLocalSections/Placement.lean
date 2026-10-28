module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Intransitivity
public import Theory.Mathieu.M24.LocalGeometry.LinearFourPlacement.Orbits

/-!
# Octad placement from the two local action steps

Every intransitive Sylow overgroup in the native M₂₄ preserves an actual
octad, by the explicit orbit calculation and Sylow conjugacy. Consequently
local normalization and nontransitivity of normalized L₄(2) joins imply
the required common-octad placement.

The local C-component condition supplies relative normalization inside the
join. The normalized-join theorem then excludes transitivity using the actual
L₄(2) quotient. Combining these proved steps establishes `octadPlacement`
without any additional premise.

Source: Aschbacher–Smith, A.3.12(14), printed pp.47–48;
GLS3, Table 5.3e.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

open Sporadic.Mathieu.M24LocalGeometry.LinearFourPlacement

/-- Assembly from the two independent local-action contracts. -/
public theorem octadPlacement_of_normalization_of_intransitivity
    (hn : LocalNormalization) (hi : NormalizedJoinIntransitivity) : OctadPlacement := by
  intro B S hB hlocal
  exact intransitive_sylow_overgroup_le_octadStabilizer S (B ⊔ S.toSubgroup)
    le_sup_right (hi B S hB (hn B S hB hlocal))

/-- A source-local L₄(2) section and the ambient Sylow two-subgroup preserve
one octad of the native Witt design. -/
public theorem octadPlacement : OctadPlacement :=
  octadPlacement_of_normalization_of_intransitivity
    localNormalization normalizedJoinIntransitivity

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
