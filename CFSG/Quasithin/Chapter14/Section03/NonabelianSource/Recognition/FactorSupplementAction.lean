module
public import Theory.GroupAction.CommonAxisCentralDisplacement
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplement
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerFactorGeometry

/-!
# The action of the original centralizer supplement

The elementary factors meet the quaternion closure in subgroups of order
eight. The centralizer supplement fixes this hyperplane and displaces every
vector into the marked point of order two. Evaluation outside the fixed
hyperplane therefore bounds its actual conjugation image by two.
The original solvable-source wrapper derives all geometric premises.
Source: Aschbacher--Smith, Quasithin Groups, 14.3.19(1)--(2), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory


open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem source_factor_supplement_action_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let D := Q⊓centralizer (F.U:Set G)
    Q=F.U⊔D ∧ ∃ A : Subgroup G,
      A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16 ∧
      Nat.card (A⊓F.U:Subgroup G)=8 ∧
      ∃ hAN : F.I₂ (sourceResidual M Mc)⊔Q≤normalizer (A:Set G),
      ⁅A,D⁆≤F.Vi 1 ∧ D≤centralizer (A⊓F.U:Set G) ∧
      Nat.card (A.normalizerMonoidHom.comp
        (inclusion (show D≤normalizer (A:Set G) from
          inf_le_left.trans (le_sup_right.trans hAN)))).range≤2 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let D := Q⊓centralizer (F.U:Set G)
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  have hRT := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRQ := (parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hf := factor_supplement_commutator_le_center F R A
    (hRT.trans (F.invariant 1)) hRQ hAR (le_sup_right.trans hAN)
  rw [hZ] at hf
  obtain ⟨hAU,hBU⟩ := elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB hEA hEB hmax
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  refine ⟨core_eq_U_sup_centralizer F dg hZ dU,A,hAR,hVA,hEA,hAc,hAU,hAN,hf.1,hf.2,?_⟩
  exact conjugation_card_le_two_of_fixed_hyperplane A D (A⊓F.U) (F.Vi 1)
    (inf_le_left.trans (le_sup_right.trans hAN)) inf_le_left ((F.le_seed 1).trans hVA)
    hAc hAU (by simpa using F.card 1 (by decide)) hf.2 hf.1
theorem source_factor_supplement_action_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let D := Q⊓centralizer (F.U:Set G)
    Q=F.U⊔D ∧ ∃ A : Subgroup G,
      A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16 ∧
      Nat.card (A⊓F.U:Subgroup G)=8 ∧
      ∃ hAN : F.I₂ (sourceResidual M Mc)⊔Q≤normalizer (A:Set G),
      ⁅A,D⁆≤F.Vi 1 ∧ D≤centralizer (A⊓F.U:Set G) ∧
      Nat.card (A.normalizerMonoidHom.comp
        (inclusion (show D≤normalizer (A:Set G) from
          inf_le_left.trans (le_sup_right.trans hAN)))).range≤2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact source_factor_supplement_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
