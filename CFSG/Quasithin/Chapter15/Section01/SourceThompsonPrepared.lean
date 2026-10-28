module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Escape
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedSmallChiefActions

/-!
# Thompson movement from the complete chosen chief actions

The four small chief actions supply the residual centralizers of15.1.12(4).
Applying them to the actual H-star family discharges the remaining input
in the escape and movement argument of15.1.13(1--2). They also centralize
the literal fixed subgroup C_V(J₁(T)), preparing the distinct global
residual step in15.1.14(1). The chosen V is retained throughout.

Source: Aschbacher--Smith15.1.12(4)--15.1.14(1), printed pp.1090--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original15.1.13(1--2), with15.1.12(4) proved from the chosen source module. -/
theorem PreparedChosenModule.source_thompson_escape_and_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    (¬ centralizer (omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) : Set G) ≤ M) ∧
      ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥ :=
  h.thompson_escape_and_movement hG T hempty hM hmany hJ
    (fun _ hH => h.thompson_omega_centralizes_residual hG T hempty hM hJ hH)

/-- Every actual outside-local residual centralizes the same chosen V_E. -/
theorem PreparedChosenModule.source_thompsonFixed_local_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      (pResidual 2 H).map H.subtype ≤ centralizer (thompsonFixed T V : Set G) :=
  h.thompsonFixed_local_residuals T hM
    (fun _ hH => h.thompson_omega_centralizes_residual hG T hempty hM hJ hH)

end CFSG.Quasithin.Chapter15.Section01
