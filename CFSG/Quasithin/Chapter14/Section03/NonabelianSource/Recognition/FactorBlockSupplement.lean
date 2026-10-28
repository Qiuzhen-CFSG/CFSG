module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockNormalizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockUFixer
public import Theory.GroupTheory.NormalizerFixerCounting

/-!
# The original centralizing supplement embeds in the dihedral fixer

The supplement D = O₂(H) intersect C_G(U) normalizes the generated block K.
Its conjugation action is faithful because C_G(K) is trivial, and fixes the
original U pointwise. The same marked split isomorphism carries A and U to
the canonical model, where the full fixer of U is dihedral of order eight.
This gives the actual supplement embedding and its order bound. Its intersection
with K is the central point of U, so its order is twice the normalizer index.
At index four the faithful normalizer action realizes every automorphism of K;
the pointwise fixer of A then forces A to be properly contained in C_G(A).

Source: Aschbacher–Smith 14.3.19(6), using 14.3.19(10).
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SixNaturalSplit
variable {G : Type*} [Group G] [Finite G]

theorem factor_block_supplement_action_of_full_orthogonal
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ f : K ≃* Model,
      (A.subgroupOf K).map f.toMonoidHom=translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=canonicalCore ∧
      ∃ j : D →* fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K),
        Function.Injective j ∧
        (∀ d : D, ∀ k : K, ((j d : MulAut K) k : G) =
          (d : G) * (k : G) * (d : G)⁻¹) ∧
        Nonempty (fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K) ≃*
          DihedralGroup 4) ∧ Nat.card D ≤ 8 := by
  intro N Y K D
  have hN := (factor_block_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  have hDN : D ≤ normalizer (K : Set G) := by
    rw [hN]
    exact le_sup_right
  have hC : centralizer (K : Set G)=⊥ := factor_block_centralizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hf : Function.Injective K.normalizerMonoidHom := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [normalizerMonoidHom_ker,hC]
    ext x
    change (x:G)=1 ↔ x=1
    exact ⟨fun hx=>Subtype.ext hx,fun hx=>congrArg Subtype.val hx⟩
  let j := normalizerCentralizerHom K D F.U hDN inf_le_right
  have hj : Function.Injective j :=
    normalizerCentralizerHom_injective K D F.U hDN inf_le_right hf
  obtain ⟨f,hA,hU⟩ := factor_block_marked_U_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hU' : (F.U.subgroupOf K).map f.toMonoidHom=canonicalCore := hU
  let eU := MulAut.fixingSubgroupEquivOfMap f (F.U.subgroupOf K) canonicalCore hU'
  obtain ⟨eD⟩ := canonicalFixer_dihedral natural_block_normalizer
  have hc : Nat.card (fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K))=8 :=
    (Nat.card_congr eU.toEquiv).trans (canonicalFixer_card natural_block_normalizer)
  refine ⟨f,hA,hU',j,hj,?_,⟨eU.trans eD⟩,?_⟩
  · intro d k
    exact normalizerCentralizerHom_apply K D F.U hDN inf_le_right d k
  · exact (Nat.card_le_card_of_injective j hj).trans_eq hc

theorem source_factor_block_supplement_action_of_solvable
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ f : K ≃* Model,
      (A.subgroupOf K).map f.toMonoidHom=translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=canonicalCore ∧
      ∃ j : D →* fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K),
        Function.Injective j ∧
        (∀ d : D, ∀ k : K, ((j d : MulAut K) k : G) =
          (d : G) * (k : G) * (d : G)⁻¹) ∧
        Nonempty (fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K) ≃*
          DihedralGroup 4) ∧ Nat.card D ≤ 8 := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_supplement_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem factor_block_supplement_dihedral_embedding_of_full_orthogonal
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ j : D →* DihedralGroup 4, Function.Injective j ∧ Nat.card D ≤ 8 := by
  intro D
  obtain ⟨f,hA,hU,j,hj,hact,⟨eD⟩,hc⟩ := factor_block_supplement_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  exact ⟨eD.toMonoidHom.comp j,eD.injective.comp hj,hc⟩

theorem source_factor_block_supplement_dihedral_embedding_of_solvable
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ j : D →* DihedralGroup 4, Function.Injective j ∧ Nat.card D ≤ 8 := by
  intro D
  obtain ⟨f,hA,hU,j,hj,hact,⟨eD⟩,hc⟩ := source_factor_block_supplement_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  exact ⟨eD.toMonoidHom.comp j,eD.injective.comp hj,hc⟩

theorem factor_block_supplement_index_of_full_orthogonal
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    K⊓D=F.Vi 1 ∧
      Nat.card D=2*K.relIndex (normalizer (K:Set G)) := by
  intro N Y K D
  have hKH := factor_block_point_stabilizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hJQ := (factor_point_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  have hKQ : K⊓F.H.pCoreIn 2=F.U := by
    calc
      K⊓F.H.pCoreIn 2 = (K⊓F.H)⊓F.H.pCoreIn 2 := by
        rw [inf_assoc,inf_eq_right.mpr (pCoreIn_le 2 F.H)]
      _ = F.U := by rw [hKH]; exact hJQ
  have hKD : K⊓D=F.Vi 1 := by
    change K⊓(F.H.pCoreIn 2⊓centralizer (F.U:Set G))=F.Vi 1
    rw [←inf_assoc,hKQ,←centerIn_eq_inf_centralizer]
    exact hZ
  refine ⟨hKD,?_⟩
  have hN := (factor_block_normalizer_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  have hh := card_supplement_eq_inf_mul_relIndex K D hN
  rw [hKD] at hh
  have hz : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  rwa [hz] at hh

theorem source_factor_block_supplement_index_of_solvable
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    K⊓D=F.Vi 1 ∧
      Nat.card D=2*K.relIndex (normalizer (K:Set G)) := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_supplement_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem source_factor_block_supplement_dihedral_iff_of_solvable
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
    let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    (Nonempty (D ≃* DihedralGroup 4) ↔
      K.relIndex (normalizer (K:Set G))=4 ∧ A<centralizer (A:Set G)) := by
  intro N Y K D
  have hDi := (source_factor_block_supplement_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  change Nat.card D=2*K.relIndex (normalizer (K:Set G)) at hDi
  obtain ⟨j,hj,hDc⟩ := source_factor_block_supplement_dihedral_embedding_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hcore := source_factor_block_core_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hKc : Nat.card K=5760 := hcore.2.2.2.1
  have hAK : A≤K := hcore.1 ▸ pCoreIn_le 2 K
  have hfaith := source_factor_block_normalizer_faithful_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hAut := source_factor_block_automorphisms_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hAcfix : Nat.card (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K))=32 :=
    hAut.2.2.2.1
  have hAutc : Nat.card (MulAut K)=23040 := hAut.2.2.2.2
  constructor
  · rintro ⟨eD⟩
    have hD8 : Nat.card D=8 := (Nat.card_congr eD.toEquiv).trans (DihedralGroup.nat_card (n := 4))
    have hi : K.relIndex (normalizer (K:Set G))=4 := by omega
    refine ⟨hi,?_⟩
    have hNc := relIndex_mul_relIndex (⊥:Subgroup G) K (normalizer (K:Set G))
      bot_le K.le_normalizer
    simp only [relIndex_bot_left] at hNc
    have hcN : Nat.card (normalizer (K:Set G))=23040 := by
      rw [hKc,hi] at hNc
      exact hNc.symm
    have hsurj : Function.Surjective K.normalizerMonoidHom :=
      (hfaith.bijective_of_nat_card_le (by rw [hAutc,hcN])).2
    have hAA : A≤centralizer (A:Set G) := by
      intro a ha x hx
      exact congrArg Subtype.val (mul_comm (⟨x,hx⟩:A) ⟨a,ha⟩)
    apply lt_centralizer_of_surjective_normalizer_action K A hAK hAA hsurj
    rw [hAc,hAcfix]
    decide
  · intro hi
    have hD8 : Nat.card D=8 := by rw [hDi,hi.1]
    exact ⟨MulEquiv.ofBijective j (hj.bijective_of_nat_card_le (by
      rw [DihedralGroup.nat_card,hD8]))⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
