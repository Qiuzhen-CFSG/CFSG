module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalGeneration
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalLinearClasses

/-!
# The original solvable application with its generating pair constructed

The marked augmentation action supplies the normalizer supplement, and
its original centralizer and plane normalizer generate LT. Applying these
constructions to the retained linear-amalgam assembly removes both extra
geometric premises from ambient symplectic recognition and the four-class
identification. Every residual, parabolic and conjugacy class remains on
the original subgroups.

The case-(ii) component, relative Thompson normality and overgroup formula
are still explicit conclusions of the earlier 13.4.7. They are not proved
by these adapters. Selecting that case from the genuine alternatives remains
with qt-d-1341-solvable-source; proving 13.4.7 and discharging the genuine
earlier 13.2–13.3 inputs and universal Structural1222 remain with
qt-d-1341-fixed-core-source. This does not complete 13.4.8–9.
Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Ambient recognition with the original inside generating pair and
normalizer supplement proved from the marking and local product. -/
theorem isPSp_of_original_R1_linear_component
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hlinear :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∃ K : Subgroup G, (T : Subgroup G) ≤ normalizer (K : Set G) ∧
        X = K ⊔ (T : Subgroup G) ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL))
    (hnormal :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      (I ⊔ (T : Subgroup G)) ⊔ B ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∀ Y : Subgroup G, Y ∈ Chapter1.HOver G (X : Set G) →
        (Y : Set G) = (X : Set G) *
          (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  have hg := (original_R1_inside_generation h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT).2
  exact isPSp_of_original_R1_linear_amalgam h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hg
    (normalizer_component_centralizer_supplement h structural D m z) hlinear hnormal supplement

/-- The same constructed generating pair yields the four actual E-classes
on the original third vertex's two-core. -/
theorem original_R1_linear_component_four_classes
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hlinear :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∃ K : Subgroup G, (T : Subgroup G) ≤ normalizer (K : Set G) ∧
        X = K ⊔ (T : Subgroup G) ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let X := (I ⊔ (T : Subgroup G)) ⊔ B
    let E := generated (normalizer (L : Set G)) z.val X
    ∃ r : Fin 4 → X.pCoreIn 2,
      (∀ i, (r i).val ≠ 1 ∧ (r i).val ^ 2 = 1) ∧
      (∀ a ∈ E, a ^ 2 = 1 → a ≠ 1 →
        ∃! i : Fin 4, ∃ g ∈ E, MulAut.conj g a = (r i).val) := by
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  have hg := (original_R1_inside_generation h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT).2
  exact original_R1_linear_amalgam_four_classes h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hg
    (normalizer_component_centralizer_supplement h structural D m z) hlinear

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
