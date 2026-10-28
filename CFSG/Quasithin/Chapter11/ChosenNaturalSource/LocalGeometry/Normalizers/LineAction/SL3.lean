module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.SL3Terminal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.RadicalCentralization

/-!
# The complete linear-three line-normalizer branch

If the Sylow normalizer escaped N_G(L), the full source component catalogue
would construct the actual J₁ configuration. The linear-three terminal
contradiction excludes this configuration, including field order four.
The resulting containment discharges the last line-action normalizer input
for the full SL₃ natural family. The original line, section centralizer and
radical stay unchanged throughout.

The only explicit remaining source input in the two-clause consumer is the
already authorized radical alternative, discharged by
qt-d-1222-natural-normalizer-source. The Sp₄(4) and G₂(4) Sylow-normalizer
terminal branches remain with qt-d-1222-natural-line-action.

Source: Aschbacher--Smith 3.3.16, p.591, and 11.2.3, pp.768--769.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

include D S m in
/-- Source Sylow-normalizer containment for every marked nonbinary SL₃ natural module. -/
theorem sl3_sylow_normalizer_le :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨A⟩ := SylowNormalizer.oddSupplement_nonempty T
  obtain ⟨E⟩ := SylowNormalizer.exists_janko_configuration (SL3.flag D S m) A hescape
  exact SylowNormalizer.SL3Terminal.false_of_sl3 D S m E

/-- Both original 11.2.3 conclusions in the linear-three branch. -/
theorem chosen_sl3_source_11_2_3
    (f : InvariantFlag (Coordinates.sl3 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_sl3_source_11_2_3_of_sylow_normalizer D S m f hX
    (sl3_sylow_normalizer_le D S m) hradical

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
