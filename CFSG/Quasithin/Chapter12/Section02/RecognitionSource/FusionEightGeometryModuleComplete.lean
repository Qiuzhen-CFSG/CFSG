module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModule
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryModuleSupplement

/-!
# The reduced FF point span under the original A₈ hypotheses

For E = Ω₁Z(C_T(v)), the subgroup W is literally the L-conjugate span
⟨Eᴸ⟩. The proved point-Sylow supplement T ≤ L ∨ C_T(v) makes W normal
in LT. The core-centralizer and Thompson arguments then give elementarity,
W ≤ T, reducedness relative to LT, and the FF property for its faithful
conjugation image. Every premise of the intermediate construction is
discharged here using the original marked action and local hypotheses.

The nonconstant seed is the marked weight-two point v, as proved in
FusionEightGeometrySeed. NoEscape is retained in the source interface;
the construction already follows from the supplied fusion configuration.
The later fixed-supplement decomposition and omega-center containment are
separate conclusions, not inputs to this construction.

Source: Aschbacher--Smith, 12.2.16, last paragraph, printed p.800.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual point span is the reduced FF-module required by original 12.2.16. -/
theorem pointSpanModule (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (_hnone : NoEscape L V) : C.PointSpanModule :=
  C.pointSpanModule_of_pointSylow_supplement h D structural
    (C.pointSylow_supplement h D structural)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
