module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingComplete
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedFree
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryComplete

/-!
# Global TI in all seven original module rows

The fixed-free rows are complete. In the reducible rows the actual module
models prove Sylow-normalizer containment, which discharges the A₆ and G₂
fusion arguments. The surviving A₈ seed is adjusted on the literal C_T(v),
and its original point-Sylow omega-center theorem contradicts the adjusted
outside conjugator. Hence the original V is globally TI.

Only Structural1222 and the precise ModuleAlternatives1222 remain as the
permitted earlier-source inputs. The universal wrapper consumes the genuine
module theorem explicitly; its producer and final discharge remain with
qt-d-1222-modules and qt-d-1222-source. The actual 12.2.13 application removes
its global-TI callback; local construction and recognition stay with
qt-d-1222-recognition. No unconditional classification is asserted here.

Source: Aschbacher–Smith 12.2.2(3) and 12.2.16, printed pp.795,799–800.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Complete reducible reduction, retaining the original V and adjusted A₈ configuration. -/
theorem reducible_of_module_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D) (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  have hNT := FusionReducibleNormalizer.sylow_normalizer_le_of_module_alternatives
    h D structural hnone hne rows
  exact reducible_of_geometric_rows h D structural hnone rows hne
    (alternating_of_sylow_normalizer h D structural hnone hne hNT)
    (globalTI_of_g2_row h D structural hnone hNT hne)

/-- Source 12.2.16 on every original choice, conditional only on its earlier source rows. -/
theorem globalTI_of_module_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D) : IsTISubgroup V :=
  globalTI_of_row_reductions_of_eight_geometry h D structural hnone
    (globalTI_of_fixedFree_module_alternatives h D structural hnone rows)
    (reducible_of_module_alternatives h D structural hnone rows)

/-- The universal source implication from the genuine seven-module theorem. -/
theorem globalTI_of_modules
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V) :
    IsTISubgroup V :=
  globalTI_of_module_alternatives h D structural hnone (modules G T L V h D)

/-- Actual application to the original 12.2.13 assembly: global TI is discharged. -/
theorem alternatives_of_modules_and_local_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (rows : ModuleAlternatives1222 D)
    (localStep : NoEscape L V → IsTISubgroup V → ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ d, SplitLinearConfiguration L V d → NoEscape L V → RecognizedGroup G d) :
    Alternatives12213 T L V :=
  alternatives_of_source_steps (fun hn => globalTI_of_module_alternatives h D structural hn rows)
    localStep recognize

/-- Universal 12.2.13 assembly with the completed source 12.2.16 supplied. -/
theorem theorem12213_of_modules_and_local_recognition
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (localStep : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
      Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V → NoEscape L V →
        IsTISubgroup V → ∃ d, SplitLinearConfiguration L V d)
    (recognize : ∀ (X : Type u) [Group X] [Finite X]
      (T : Sylow 2 X) (L V : Subgroup X) (d : ℕ),
      Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
        SplitLinearConfiguration L V d → NoEscape L V → RecognizedGroup X d) :
    Theorem12213.{u} KnownSimple.IsKnownSimple :=
  theorem12213_of_source_steps KnownSimple.IsKnownSimple
    (fun _ _ _ _ _ _ h D hn => globalTI_of_modules h D structural modules hn)
    localStep recognize

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
