module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockPointCore
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockSplit
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.PointAlignment
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockPointStabilizer

/-!
# The original quaternion subgroup under a marked split isomorphism

The point stabilizer in K is the actual join RY. Its two-residual has
quaternion two-core U. Since H is the centralizer of the nontrivial flag
point, this identifies U intrinsically inside K. Functorial transport and
an even coordinate permutation then carry the original A and U, through
the same split isomorphism, to translations and the canonical point core.

Source: Aschbacher–Smith 14.3.19(10), printed p.997. The canonical point core
is written as its literal centralizer/residual/core expression, definitionally
`BinaryPermutation.SixNaturalSplit.canonicalCore` in the model calculation.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

private theorem factor_block_point_core_of_intersection
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
    K⊓F.H=(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y →
    ∀z:K,(z:G)∈F.Vi 1 → z≠1 →
      pointCentralizerTwoResidualCore z=F.U.subgroupOf K := by
  intro N Y K hKH z hz hz1
  have hU:Y.pCoreIn 2=F.U := factor_point_residual_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hUK:F.U≤K := hU ▸ (pCoreIn_le 2 Y).trans le_sup_right
  have hH:F.H=centralizer ({(z:G)}:Set G) := by
    have hc:Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
    have hzG:(z:G)≠1 := fun he=>hz1 (Subtype.ext he)
    obtain ⟨u,hu,huniq⟩ := (Nat.card_eq_two_iff' (1:F.Vi 1)).mp hc
    have hzsub:(⟨(z:G),hz⟩:F.Vi 1)≠1 := fun he=>hzG (congrArg Subtype.val he)
    apply le_antisymm
    · exact (normalizer_le_centralizer_of_card_two (F.Vi 1) hc).trans
        (centralizer_le (Set.singleton_subset_iff.mpr hz))
    · intro x hx
      apply _root_.centralizer_le_normalizer (F.Vi 1)
      intro v hv
      by_cases hv1:v=1
      · simp [hv1]
      have hvsub:(⟨v,hv⟩:F.Vi 1)≠1 := fun he=>hv1 (congrArg Subtype.val he)
      have hvz:v=(z:G) := congrArg Subtype.val ((huniq ⟨v,hv⟩ hvsub).trans
        (huniq ⟨(z:G),hz⟩ hzsub).symm)
      rw [hvz]
      exact (mem_centralizer_singleton_iff.mp hx).symm
  apply pointCentralizerTwoResidualCore_eq_subgroupOf K F.U z hUK
  rw [←hH,hKH]
  exact factor_point_join_residual_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

private theorem factor_block_point_aligned_of_intersection
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
    K⊓F.H=(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y →
    ∃f:K≃*BinaryPermutation.SixNaturalSplit.Model,
      (A.subgroupOf K).map f.toMonoidHom=BinaryPermutation.SixNaturalSplit.translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=pointCentralizerTwoResidualCore
        (SemidirectProduct.inl (Multiplicative.ofAdd
          (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)):
            BinaryPermutation.SixNaturalSplit.Model) := by
  intro N Y K hKH
  obtain ⟨hAK,qA,eK,heA,hA⟩ := factor_block_split_model_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hc:Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1:F.Vi 1)).mp hc
  have hzA:(z:G)∈A := hVA (F.le_seed 1 z.property)
  let zK:K := ⟨z,hAK hzA⟩
  have hzK:zK≠1 := fun he=>hz (Subtype.ext (show (z:G)=1 from congrArg (fun x:K=>(x:G)) he))
  have hU:pointCentralizerTwoResidualCore zK=F.U.subgroupOf K :=
    factor_block_point_core_of_intersection
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
      hKH zK z.property hzK
  obtain ⟨f,hf,_,hfU⟩ := BinaryPermutation.SixNaturalSplit.exists_point_core_aligned_equiv
    (A.subgroupOf K) (F.U.subgroupOf K) eK hA zK hzA hzK hU.symm
  exact ⟨f,hf,hfU⟩

theorem factor_block_intrinsic_U_of_full_orthogonal
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
    ∀z:K,(z:G)∈F.Vi 1 → z≠1 →
      pointCentralizerTwoResidualCore z=F.U.subgroupOf K := by
  exact factor_block_point_core_of_intersection
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
    (factor_block_point_stabilizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN)

theorem factor_block_marked_U_of_full_orthogonal
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
    ∃f:K≃*BinaryPermutation.SixNaturalSplit.Model,
      (A.subgroupOf K).map f.toMonoidHom=BinaryPermutation.SixNaturalSplit.translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=pointCentralizerTwoResidualCore
        (SemidirectProduct.inl (Multiplicative.ofAdd
          (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)):
            BinaryPermutation.SixNaturalSplit.Model) := by
  exact factor_block_point_aligned_of_intersection
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
    (factor_block_point_stabilizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN)

theorem source_factor_block_intrinsic_U_of_solvable
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
    ∀z:K,(z:G)∈F.Vi 1 → z≠1 →
      pointCentralizerTwoResidualCore z=F.U.subgroupOf K := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_intrinsic_U_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem source_factor_block_marked_U_of_solvable
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
    ∃f:K≃*BinaryPermutation.SixNaturalSplit.Model,
      (A.subgroupOf K).map f.toMonoidHom=BinaryPermutation.SixNaturalSplit.translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=pointCentralizerTwoResidualCore
        (SemidirectProduct.inl (Multiplicative.ofAdd
          (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)):
            BinaryPermutation.SixNaturalSplit.Model) := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_block_marked_U_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
