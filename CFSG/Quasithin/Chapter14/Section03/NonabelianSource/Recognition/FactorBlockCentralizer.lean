module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorGeneratedResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorNormalizerSylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable
public import CFSG.Quasithin.Chapter14.Section06.SourceResidualCentralizer
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Faithful ambient action on the original alternating-six block

The original RQ normalizes both generators of K. Its Sylow maximality in
N_G(A) therefore forces the two-group C_G(K) into RQ and hence T. Since
L is contained in K, the already proved C_T(L)=1 gives C_G(K)=1. The
normalizer consequently acts faithfully on the literal K by conjugation.
No automorphism classification or stronger centralizer equality is needed.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(5), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_block_centralizer_of_full_orthogonal
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
    centralizer (K:Set G)=⊥ := by
  intro N Y K
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let S := R⊔Q
  let NG := normalizer (A:Set G)
  let C := centralizer (K:Set G)
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hRU := (factor_generated_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN).2.2.1
  have hAK : A≤K := hAR.trans (le_sup_left.trans hRU)
  have hCN : C≤NG := (centralizer_le hAK).trans (_root_.centralizer_le_normalizer A)
  have hCp : IsPGroup 2 C := (factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8).2.to_le (centralizer_le hAK)
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hTH:(T:Subgroup G)≤F.H := F.invariant 1
  have hQT:Q≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change Q≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hQN:Q≤N := le_inf (pCoreIn_le 2 _) (le_sup_right.trans hAN)
  have hQK:Q≤normalizer (K:Set G) :=
    (le_inf (hQT.trans h.sylow_normalizes_L)
      (hQN.trans (le_normalizer_embedded_pResidual 2 N))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSK:S≤normalizer (K:Set G) :=
    sup_le ((le_sup_left.trans hRU).trans K.le_normalizer) hQK
  have hSC:S≤normalizer (C:Set G) := hSK.trans (normalizer_le_normalizer_centralizer K)
  obtain ⟨_,_,P,hP⟩ := factor_normalizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN
  change (P:Subgroup NG).map NG.subtype=S at hP
  have hPN:(P:Subgroup NG)≤normalizer (C.subgroupOf NG:Set NG) := by
    intro p hp
    apply le_normalizer_comap NG.subtype
    apply hSC
    rw [←hP]
    exact mem_map_of_mem NG.subtype hp
  have hCS:C≤S := by
    have hh := hCp.comap_subtype.le_sylow_of_normalized P hPN
    intro c hc
    rw [←hP]
    exact mem_map_of_mem NG.subtype (hh (show (⟨c,hCN hc⟩:NG)∈C.subgroupOf NG from hc))
  apply le_bot_iff.mp
  have hCL:C≤centralizer (sourceResidual M Mc:Set G) := centralizer_le (show sourceResidual M Mc≤K from le_sup_left)
  exact (le_inf (hCS.trans (sup_le hRT hQT)) hCL).trans
    (Chapter14.Section06.source_residual_sylow_centralizer_eq_bot
      hG T hempty hM hu hmany hcard e).le

theorem source_factor_block_centralizer_of_solvable
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
    centralizer (K:Set G)=⊥ := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_centralizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem source_factor_block_normalizer_faithful_of_solvable
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
    Function.Injective K.normalizerMonoidHom := by
  intro N Y K
  have hc : centralizer (K:Set G)=⊥ := source_factor_block_centralizer_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker,hc]
  ext x
  change (x:G)=1 ↔ x=1
  exact ⟨fun hx=>Subtype.ext hx,fun hx=>congrArg Subtype.val hx⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
