module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerIntersection
public import Theory.GroupTheory.ElementaryFactorQuaternionIntersection

/-! The chosen original factors meet U in elementary eights. The preceding
parabolic intersection identifies R∩U with W; involution generation of W
and the quaternion rank bound determine the orders. This retains the literal
A,B needed in14.3.18(6) and14.3.19(2). -/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem elementary_factor_core_intersections_of_full_orthogonal
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
    (A B:Subgroup G)
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hBR:B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hVB:rankTwoSeed T M≤B)
    (hEA:IsElementaryAbelian 2 A) (hEB:IsElementaryAbelian 2 B)
    (hmax:∀E:Subgroup G,IsElementaryAbelian 2 E→
      E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A∨E≤B) :
    Nat.card (A⊓F.U:Subgroup G)=8 ∧ Nat.card (B⊓F.U:Subgroup G)=8 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  obtain ⟨hRQ,_,_,_,_⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hRU:R⊓F.U=F.W := le_antisymm
    ((inf_le_inf_left R hUQ).trans hRQ.le)
    (le_inf (hRQ.ge.trans inf_le_left) inf_le_left)
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi:(frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hsquare:∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan:F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last];rfl
  have hindex:F.W.relIndex F.U=2 := F.binary_U_action_index (by decide)
    (sourceResidual M Mc) (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e).L_normalizes_seed
    hsquare hspan hne
  have hWc:Nat.card F.W=16 := by
    have hh:=relIndex_mul_card_of_le (show F.W≤F.U from inf_le_left)
    rw [hindex,dU.card] at hh
    omega
  have hVc:Nat.card (rankTwoSeed T M)=4 := by
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  exact quaternion_factor_intersection_card_eight F.U R F.W (rankTwoSeed T M) A B dU
    hAR hBR hRU hWc hVc F.seed_le_W hVA hVB hEA hEB hmax
    (W_involution_generated_of_full_orthogonal F dg hZ hne hr)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
