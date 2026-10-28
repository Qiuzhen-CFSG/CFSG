module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSFieldComparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2

/-!
# The original G₂ line-normalizer theorem

The reciprocal critical actions exclude the field-four MS escape, completing
Sylow-normalizer containment for the full nonbinary G₂ family. This discharges
the last normalizer premise in both original 11.2.3 conclusions, retaining the
literal flag, centralizer, radical and quotient-section action.

Only the authorized radical alternative remains explicit. Its discharge and
final source assembly belong to qt-d-1222-natural-normalizer-source.
Source: Aschbacher--Smith 3.3.16, p.591, and 11.2.3, pp.768--769;
Meierfrankenfeld--Stellmacher (1993), (3.2), pp.865--866.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Both original 11.2.3 conclusions in the G₂ branch. -/
theorem chosen_g2_source_11_2_3
    (f : InvariantFlag (Coordinates.g2 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_g2_source_11_2_3_of_sylow_normalizer D S m f hX
    (SylowNormalizer.G2MS.g2_sylow_normalizer_le D S m) hradical

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
