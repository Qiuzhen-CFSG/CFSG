module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Cyclic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.Reduction

/-!
# The diagram Hall--Cartan construction from the covered Borel calculation

The source-marked diagram model constructs its cyclic subgroup directly,
including the torus inside the literal derived symplectic group. Combining
this with the proved overlap reduction produces the intrinsic Hall--Cartan
witness under the explicit covered-Borel hypothesis.

The PSL₃ and Sp₄′ central-cover calculations remain obligations of the
respective model branches. This conditional application is not a proof of
the unconditional diagram branch of E.6.27.
Source: Aschbacher--Smith, E.2.2(2b), pp.215--216; E.6.27, p.257;
and the Frattini step of 4.4.13, pp.623--624.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterB DiagramHall
variable {X : Type*} [Group X] [Finite X]

/-- Actual application to the source cyclic subgroup and original Sylow.
The two concrete covered-Borel producers must discharge `hb` in final assembly. -/
theorem diagram_intrinsic_of_borelControl (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hn : 1 < generationParameter X)
    (hm : DiagramModel (minimalParabolicMax S hP) K S (generationParameter X))
    (hb : CoveredBorelControl S hP K) :
    Nonempty (IntrinsicHallCartanData S hP (generationParameter X)) :=
  intrinsic_of_cyclic_and_hallControl S hP (by omega)
    (hallControl_of_coveredBorel S hP hK hc hb) hm.cyclic


end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
