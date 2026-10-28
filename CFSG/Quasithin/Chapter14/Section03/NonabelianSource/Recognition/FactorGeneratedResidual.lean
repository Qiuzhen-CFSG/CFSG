module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorPointResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorGlobalCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicResidual
public import Theory.GroupTheory.PResidual.FiniteLocalPair

/-!
# The generated group in the original elementary-factor branch

The residual of the point normalizer remains the residual after adjoining
R. Together with the original parabolic residual it generates a two-perfect
group containing RU. The global centralizer of A normalizes both generators
and hence their join. These identities keep the original embedded residuals
needed by the alternating-six action calculation.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(4), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_generated_residual_geometry_of_full_orthogonal
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
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let J := R⊔Y
    let K := sourceResidual M Mc⊔Y
    (pResidual 2 J).map J.subtype=Y ∧ IsPPerfect 2 K ∧
      R⊔F.U≤K ∧ centralizer (A:Set G)≤normalizer (K:Set G) := by
  intro R N Y J K
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨hL,_,hcore,_⟩ := parabolic_residual_core_structure_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRN:R≤N := le_inf (hRT.trans (F.invariant 1))
    ((pCoreIn_le 2 _).trans (le_sup_left.trans hAN))
  have hRY:R≤normalizer (Y:Set G) := hRN.trans (le_normalizer_embedded_pResidual 2 N)
  have hYp:IsPPerfect 2 Y := isPPerfect_embedded_pResidual_of_finite 2 N
  have hres:(pResidual 2 J).map J.subtype=Y := by
    change (pResidual 2 (R⊔Y:Subgroup G)).map (R⊔Y).subtype=Y
    rw [sup_comm R Y]
    exact embedded_pResidual_join_pGroup Y R hYp (isPGroup_pCoreIn 2 _) hRY
  have hKp:IsPPerfect 2 K := isPPerfect_sup _ _
    ((pResidual_eq_top_iff 2 _).mp h.L_residual) hYp
  have hRL:R≤sourceResidual M Mc := by
    change (F.I₂ (sourceResidual M Mc)).pCoreIn 2≤sourceResidual M Mc
    rw [←hcore]
    exact pCoreIn_le 2 _
  have hUY:F.U≤Y := (factor_point_residual_fixed_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).2.1
  have hCH:centralizer (A:Set G)≤F.H := (factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8).1
  have hCM:centralizer (A:Set G)≤M := (centralizer_le hVA).trans h.seed_centralizer_le
  have hCL:centralizer (A:Set G)≤normalizer (sourceResidual M Mc:Set G) :=
    hCM.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc))
  have hCY:centralizer (A:Set G)≤normalizer (Y:Set G) :=
    (le_inf hCH (_root_.centralizer_le_normalizer A)).trans (le_normalizer_embedded_pResidual 2 N)
  exact ⟨hres,hKp,sup_le (hRL.trans le_sup_left) (hUY.trans le_sup_right),
    (le_inf hCL hCY).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
