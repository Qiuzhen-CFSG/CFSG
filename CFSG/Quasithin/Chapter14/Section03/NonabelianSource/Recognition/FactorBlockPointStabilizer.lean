module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockCore
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import Theory.GroupTheory.TransitiveInvolutionNormalizer.Card

/-!
# The original point stabilizer in the alternating-six block

The marked natural A₆ action is transitive on the fifteen nonidentity
vectors of A. Since |K|=5760, the stabilizer of the original point V₁ has
order384. The original subgroup J=R O²(N_H(A)) lies in K∩H and already has
order384, proving equality of the literal subgroups.

This identifies the point parabolic needed to recover the quaternion
subgroup U as the two-core of its embedded two-residual.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19, printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

/-- The point stabilizer inside the original block is the original residual join. -/
theorem factor_block_point_stabilizer_of_full_orthogonal
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
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    K⊓F.H = (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y := by
  intro N Y K
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let J := R⊔Y
  obtain ⟨B,hBR,hEB,hAB,hRc⟩ : ∃ B:Subgroup G, B≤R ∧ IsElementaryAbelian 2 B ∧
      A⊔B=R ∧ Nat.card R=64 := by
    obtain ⟨C,B,hCR,hBR,hVC,hVB,hEC,hEB,hCc,hBc,hCBi,hCB,hRc,hCN,hBN,hmax⟩ :=
      maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
        F dg hZ hne g hgP hgH hr
    rcases hmax A inferInstance hAR with hac|hab
    · have heq:A=C := eq_of_le_of_card_ge hac (by rw [hAc,hCc])
      exact ⟨B,hBR,hEB,by simpa [heq] using hCB,hRc⟩
    · have heq:A=B := eq_of_le_of_card_ge hab (by rw [hAc,hBc])
      exact ⟨C,hCR,hEC,by simpa [heq,sup_comm] using hCB,hRc⟩
  let := hEB
  have hKc:Nat.card K=5760 := (factor_block_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN).2.2.2.1
  obtain ⟨hKA,eA,qA,hqA⟩ := factor_alternating_natural_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN
  have hcount := card_point_normalizer_of_transitive
    A K (F.Vi 1) hKA ((F.le_seed 1).trans hVA) (by simpa using F.card 1 (by decide))
    (BinaryPermutation.exists_conjugator_of_alternatingSix_natural_action A K hKA eA qA hqA)
  change (Nat.card A-1)*Nat.card (K⊓F.H:Subgroup G)=Nat.card K at hcount
  rw [hAc,hKc] at hcount
  have hKH:Nat.card (K⊓F.H:Subgroup G)=384 := by omega
  have hJc:Nat.card J=384 := (factor_point_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN).2
  have hRU:R⊔F.U≤K := (factor_generated_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN).2.2.1
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hYN:Y≤N := map_subtype_le _
  have hJH:J≤F.H := sup_le (hRT.trans (F.invariant 1)) (hYN.trans inf_le_left)
  have hJK:J≤K := sup_le (le_sup_left.trans hRU) le_sup_right
  exact (eq_of_le_of_card_ge (le_inf hJK hJH) (by rw [hJc,hKH])).symm

/-- Point-stabilizer identification with the original solvable-source hypotheses. -/
theorem source_factor_block_point_stabilizer_of_solvable
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
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    K⊓F.H = (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_point_stabilizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
