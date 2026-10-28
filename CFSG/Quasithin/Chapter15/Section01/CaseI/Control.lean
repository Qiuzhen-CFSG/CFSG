module

public import CFSG.Quasithin.Chapter15.Section01.CaseI.Setup
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl

/-!
# Literal control package for Case I of original 15.1.15

The component argument in Case I starts with two independent pieces of source
control.  The first is the fixed subgroup `V_E = C_V(J₁(T))`, together with
the residual centralization and Thompson movement supplied by 15.1.12--13.
The second is the Baumann control of the selected local module from 15.1.9.
This leaf packages those conclusions for the actual chosen `V`; later Case-I
component/model leaves can consume the fields without replacing `V_E` by the
whole local module.

Source: Aschbacher--Smith 15.1.9, 15.1.13(1--2), and the setup of 15.1.15,
printed pp.1088--1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterB Chapter14.SourcePreliminaries Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The exact common control data used by the Case-I component argument. -/
structure CaseIControlData (T : Sylow 2 G) (M V : Subgroup G) : Prop where
  outside_star : ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M
  fixed_ne_bot : thompsonFixed T V ≠ ⊥
  fixed_le_omega : thompsonFixed T V ≤
    omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1)
  local_residual_centralizes :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      (pResidual 2 H).map H.subtype ≤
        centralizer (thompsonFixed T V : Set G)
  omega_centralizer_escape :
    ¬ centralizer
        (omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) : Set G) ≤ M
  thompson_moved : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥
  local_le_thompson_alpha : localModule T M ≤ thompsonAlpha (T : Subgroup G)
  baumann_eq : baumann (T : Subgroup G) =
    baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G))
  maximal_baumann_overgroup :
    maximalTwoLocalOvergroups
      (M ⊓ normalizer (baumann (T : Subgroup G) : Set G)) = {M}
  baumann_characteristic_closure_le :
    (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M
  baumann_normalizer_le : normalizer (baumann (T : Subgroup G) : Set G) ≤ M
  maxJ_normalizer_le :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M
  sylow_normalizer_le : normalizer (T : Set G) ≤ M

/-- Construct the common Case-I control package from the literal chosen module. -/
theorem PreparedChosenModule.caseI_control_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) : CaseIControlData T M V := by
  obtain ⟨hfixed, hle, hres, hesc, hmoved⟩ :=
    h.caseI_thompson_setup hG T hempty hM hmany hJ
  obtain ⟨halpha, hbaumann, hmax, hchar, hnb, hnj, hnt⟩ :=
    source_centralizing_baumann_control hG T hM hJ
  have hout : Chapter3.HasMaximalOutside T M := by
    obtain ⟨L, hL, K, hK, hne⟩ :=
      (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hLM : L = M
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hK.1 hM.1.2 hK.2
        (fun he => hne (hLM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hL.1 hM.1.2 hL.2 hLM
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact
    { outside_star := ⟨H, hH⟩
      fixed_ne_bot := hfixed
      fixed_le_omega := hle
      local_residual_centralizes := hres
      omega_centralizer_escape := hesc
      thompson_moved := hmoved
      local_le_thompson_alpha := halpha
      baumann_eq := hbaumann
      maximal_baumann_overgroup := hmax
      baumann_characteristic_closure_le := hchar
      baumann_normalizer_le := hnb
      maxJ_normalizer_le := hnj
      sylow_normalizer_le := hnt }

end CFSG.Quasithin.Chapter15.Section01
