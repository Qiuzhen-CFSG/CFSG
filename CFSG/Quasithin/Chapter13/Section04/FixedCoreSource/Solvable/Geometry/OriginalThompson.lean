module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationPoint

/-!
# The original module inside the first Thompson subgroup

The ordinary augmentation point-radical calculation places the original V
inside J(O₂(L₁T)). The proved equality of that two-core with the literal
first-flag action core transports this to J(R₁).

This also removes the separate containment premise before selecting the
ordinary row. In the Baumann-normalizer branch the local-product argument
already proves the ordinary quotient without that premise. In the short
branch shortness itself proves it. Each branch can therefore apply the
augmentation calculation without using the result it is meant to justify.
The original source generation, amalgam inputs and recognition consumers
use this deduction in OriginalGeneration, OriginalPlaneExistence and
OriginalGeneratedAmalgam.
Source: Aschbacher–Smith 13.2.2(6–7), 13.4.8–9, pp.877–878,904–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Transport the actual point-radical containment to the original R₁. -/
theorem module_le_original_R1_thompson_of_ordinary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m) := by
  rw [firstFlagCore_eq_firstParabolicCore h structural D m eL z hz hzL]
  exact (Nonsolvable.ordinary_augmentation_point_rank h structural D m eL z hz hzL).2

/-- The source Baumann/short alternative supplies the containment needed
by the short-block local-product proof, without assuming the ordinary row. -/
theorem module_le_original_R1_thompson
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m) := by
  rcases hcase with hB | hb
  · obtain ⟨⟨eL⟩,_⟩ := centralizer_pair_quotient_of_baumann_original_R1
      h₀ h structural D m z hz hzL hB hout h1339 hsolv hindex h1342
    exact module_le_original_R1_thompson_of_ordinary h structural D m eL z hz hzL
  · obtain ⟨eL⟩ := ordinary_of_short_core_marking D m hb
    exact module_le_original_R1_thompson_of_ordinary h structural D m eL z hz hzL

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
