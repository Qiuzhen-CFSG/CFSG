module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Frame
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Source

/-!
# Source application of the completed G₂ R₁ localization

The proved parameter family supplies s=2n on the same marking and flag.
Thus clause 11.2.2(6) requires only the earlier maximal-local uniqueness,
fixed-line and third-space normalizer conclusions. No local geometry or
numerical parameter assumption remains. The independent clause-(5)
root-plane reconstruction remains with this task; its conditional APIs
continue to retain the original full central preimages.

Source: Aschbacher--Smith 11.2.2(6), printed pp.767--768.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- The literal C₁(R₁,V) conclusion, with the source parameter value proved.
The three premises are precisely independently owned earlier-source results;
final discharge remains with qt-d-1222-natural-local-geometry. -/
theorem source_clause_six_of_preceding
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) := by
  have hs := (Parameters.source_parameters D S f hunique hthree hline).2.2.1.2
  exact source_clause_six D S m f hs hthree

/-- The original rank-one R₁ application needs only zeroth centralization
from the still-owned clause-(5) branch, besides the earlier source inputs. -/
theorem rankOne_impossible_of_preceding_and_zero_centralizes
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False := by
  have hs := (Parameters.source_parameters D S f hunique hthree hline).2.2.1.2
  exact rankOne_impossible_of_geometry D S f hs (r1FamilyLocalization D S m f)
    hthree hw H₁ P hP hn hout
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
