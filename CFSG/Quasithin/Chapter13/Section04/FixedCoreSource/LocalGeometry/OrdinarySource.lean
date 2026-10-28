module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryPointResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneSource

/-!
# Original ordinary solvable recognition with local clauses discharged

The original first action-core R₁ equals O₂(L₁T) in the ordinary A₆ row.
The augmentation Baumann theorem therefore supplies its actual
Baumann-or-short alternative. The point-residual argument supplies 13.3.9,
and the relatively normal C-component calculation supplies 13.4.2(5).
Together with the constructed plane amalgam theorem these discharge all
three local callbacks in the original solvable recognition consumer.

Under negated ambient symplectic recognition this applies at every escaping
omega point, supplying the universal nonsolvability premise required by
the nonsolvable branch, at both weights. Full normalizer fusion, the omega
fixed index, N_G(L)=LT and the genuine earlier Chapter 12/13.3 and natural
large-distance inputs remain explicit. This is not the final 13.4.1 assembly;
the covered first action-core is different and is not identified here.
Source: Aschbacher--Smith 13.2.2(7), 13.3.9, 13.4.2(5), 13.4.8--9,
printed pp.877--878,887,897,904--907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the augmentation alternative to the literal original R₁. -/
theorem ordinary_firstFlagCore_alternative
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  rw [firstFlagCore_eq_firstParabolicCore h structural D m eL z hz hzL]
  exact Nonsolvable.ordinary_augmentation_baumann_alternative_of_largeDistance
    hl h structural D m eL z hz hzL

/-- Original ordinary solvable recognition, with 13.3.9, the R₁ Baumann
alternative, the prime-to-three normalizer identity and plane1347 proved. -/
theorem ordinary_R1_recognition
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  exact Amalgam.original_R1_recognition_of_plane_source h₀ h structural D m
    (ordinary_firstFlagCore_alternative hl h structural D m eL z hz hzL)
    z hz hzL hout hfusion
    (fun Y hYH hnY hYM hp => ordinary_point_residual D m eL hM z hz hzL hYH hnY hYM hp)
    hsolv hindex (fun _ => normalizer_primeToThree_residual h structural eL)
    h1332 modules fixed covered h13316 hl hM

/-- Negated recognition gives nonsolvability at every original escaping
omega point, including both nonconstant weights. -/
theorem ordinary_universal_escaping_nonsolvable
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSp G 3 2) :
    ∀ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      z.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) := by
  intro z hz hzL hout hs
  exact hnot (ordinary_R1_recognition h₀ h structural D m eL z hz hzL hout hfusion hs
    hindex h1332 modules fixed covered h13316 hl hM)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
