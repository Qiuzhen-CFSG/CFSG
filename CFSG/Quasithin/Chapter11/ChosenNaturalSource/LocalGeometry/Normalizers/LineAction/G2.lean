module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.Comparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.RadicalCentralization

/-!
# The G₂ line-action branch and the complete marked-family consumer

The point-radical product shows that R₁ centralizes the full original V₁:
O₂(L₁) lies in the already centralizing perfect residual, and O₂(LT)
centralizes V. The component-orbit and quotient-action arguments then give
the literal Sylow image in lineSectionKernel. The final consumer covers
SL₃, Sp₄ and G₂ and uses the proved Singer normalization in the zero-fixed
branch together with the actual Frattini lifts in both branches.

Sylow-normalizer containment remains an obligation of this task,
qt-d-1222-natural-line-action, via its quotient-recognition and terminal
argument. The radical alternative remains with the authorized parent
qt-d-1222-natural-normalizer-source. These conditional consumers do not
claim that either remaining source input has been proved.
Source: Aschbacher--Smith 11.2.3, printed pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original G₂ point radical centralizes the full first flag subgroup. -/
theorem chosen_g2_radical_centralizes_line
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m)) :
    f.Ri 0 ≤ centralizer (f.Vi 0 : Set G) :=
  chosen_radical_centralizes_line_of_core_product D S f (G2Line.core_product D S m f)

/-- The actual G₂ line centralizer supplies the exact section-kernel Sylow. -/
theorem chosen_g2_line_positive_steps
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 :=
  chosen_line_positive_steps_of_flag_geometry S f
    ((SylowNormalizer.invariantFlag_geometry D S f).2.2.model 0)
    (chosen_first_centralizes_line f) (chosen_g2_radical_centralizes_line D S m f) hC

/-- Both original G₂ clauses, conditional only on the two remaining source normalizer inputs. -/
theorem chosen_g2_source_11_2_3_of_sylow_normalizer
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m)) {X : Subgroup G} (hX : IsCartan T L X)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_radical_centralization D S f hX
    (chosen_g2_radical_centralizes_line D S m f) hNT hradical

/-- Radical centralization in every marked nonbinary natural family. -/
theorem chosen_radical_centralizes_line
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    f.Ri 0 ≤ centralizer (f.Vi 0 : Set G) := by
  cases c with
  | sl3 m => exact chosen_sl3_radical_centralizes_line D S m f
  | sp4 m => exact chosen_sp4_radical_centralizes_line D S m f
  | g2 m => exact chosen_g2_radical_centralizes_line D S m f

/-- The complete hpositive input, on the literal centralizer and quotient-action kernel. -/
theorem chosen_line_positive_steps
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hC : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :
    normalizer (f.Vi 0 : Set G) ≤ normalizer (f.Li 0 : Set G) ∧
      ∃ P : Sylow 2 (lineSectionKernel (f.Vi 0) (f.Li 0)),
        (P : Subgroup _).map (lineSectionKernel (f.Vi 0) (f.Li 0)).subtype = f.Ri 0 :=
  chosen_line_positive_steps_of_flag_geometry S f
    ((SylowNormalizer.invariantFlag_geometry D S f).2.2.model 0)
    (chosen_first_centralizes_line f) (chosen_radical_centralizes_line D S f) hC

/-- Both clauses for all three families. Sylow-normalizer containment remains
with qt-d-1222-natural-line-action; the parent supplies the radical alternative. -/
theorem chosen_source_11_2_3_of_sylow_normalizer
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_radical_centralization D S f hX
    (chosen_radical_centralizes_line D S f) hNT hradical
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
