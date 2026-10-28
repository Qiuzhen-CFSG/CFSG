module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.OffenderActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Line
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.MarkedActors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Construction

/-!
# The marked natural-eight action from the universal FF classification

The actual component module has the original star kernel and hence a faithful
binary star action. Its offender-generated actor contains the marked alternating
component, has trivial two-core and has that component as generalized Fitting
subgroup. The actual moving line V₂ retains its parabolic, Sylow and Y₊ markings.
The Sylow image is Sylow, normalizes the component parabolic, and generates
the full star actor together with the component; Y₊ lies in that parabolic.
The conversion of equivariant linear coordinates into an ambient
`NaturalEightAction` preserves the supplied star marking exactly.

`actionOfSource` constructs the `NaturalEightAction` and `actionOfSource_actor`
identifies its actor with the supplied S₈ marking composed with the original
star map. The classification is applied to the offender-generated actor;
the marked moving line excludes the natural branches and the nontrivial cover.
The elementary abelian structure and all extension premises are proved.

The two explicit universal inputs are the full B.5.1(1)/B.4.2 table
`FFSpecialization.Sieve.UniversalFFClassification` and I.1.6(6) natural-module
cohomology vanishing `FFSpecialization.Sieve.UniversalNaturalCohomology`.
The actual component's SQTK hypothesis, preliminary `LineData`, Sylow witness
and middle-node marking remain explicit. This is the conditional construction
of 15.3.32(1); its source assembly must supply those inputs, and the remaining
clauses of 15.3.32 are separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
15.3.32(1), printed pp.99–100 and 1132–1133.
-/
