module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Normality
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Ordinary
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.SylowIrreducible

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.RankTwo
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.QuotientStabilizer

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.G2
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryCatalogue

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryPowerActions

/-!
# The irreducible component-normalizer branch of original 13.1.12(3)

The source component containment, actual Sylow and marked ordinary catalogue
are combined with the C.2.7 characteristic-two analysis. All ordinary and
characteristic-two alternatives are excluded, including the linear-three
central covers and the genuine triality and Ree carriers. The latter rows
use their scalar Sylow actions on the original odd Frattini quotient to
contradict the actual S₃ stabilizer section.

`Context.not_escape_of_irreducible_source_actions` is the complete local
contradiction conditional on earlier `SieveActions` and `Control`. The
literal centralizer and TI applications retain only the separate reducible
component branch besides the earlier source facts. Construction of
SieveActions remains with qt-d-1317-module-orbits and its discharge with
this source assembly; global centralizer assembly remains with
qt-d-1317-centralizer-sieve. No source model list or parabolic marking
remains an extra premise of the irreducible contradiction.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875.
-/
