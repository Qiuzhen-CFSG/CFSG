module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockSplit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.MultiplicativeNormalizer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Marked

/-!
# Automorphisms of the original split A₆ block

The original factor construction supplies a split isomorphism preserving its
chosen elementary sixteen-group. The literal natural-image normalizer is S₆;
transporting the cocycle calculation therefore gives Aut(K) ≃ 2⁵:S₆ and
identifies the pointwise fixer of A with the deleted permutation module.
The canonical complement stabilizer is S₆ under the same natural action.

Source: Aschbacher–Smith 14.3.19(10), the automorphism-group and module clauses.
The additional assertion concerning the actual quaternion subgroup U is separate.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SixNaturalSplit
variable {G:Type*} [Group G] [Finite G]

theorem natural_block_normalizer :
    normalizer (action.range : Set (MulAut Vector)) =
      (BinaryPermutation.naturalMulAction (Fin 6)).range :=
  Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.normalizer_alternatingMulImage

noncomputable def naturalBlockAutomorphismEquiv : MulAut Model ≃* AutomorphismModel :=
  automorphismEquiv natural_block_normalizer

noncomputable def naturalBlockComplementStabilizerEquiv :
    MulAction.stabilizer (MulAut Model) (complement : Set Model) ≃* Equiv.Perm (Fin 6) :=
  complementStabilizerEquiv natural_block_normalizer

theorem factor_block_automorphisms_of_full_orthogonal
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
    Nonempty (MulAut K ≃* AutomorphismModel) ∧
      Nonempty (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K) ≃*
        Multiplicative (BinaryPermutation.Deleted (Fin 6))) ∧
      IsElementaryAbelian 2 (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K)) ∧
      Nat.card (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K))=32 ∧
      Nat.card (MulAut K)=23040 := by
  intro N Y K
  obtain ⟨hAK,qA,eK,heA,hA⟩ := factor_block_split_model_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hm : (A.subgroupOf K).map eK.toMonoidHom=translations := hA
  let eJ := markedAutomorphismEquiv eK natural_block_normalizer
  refine ⟨⟨eJ⟩,⟨markedKernelEquiv (A.subgroupOf K) eK hm⟩,
    markedKernel_elementary (A.subgroupOf K) eK hm,
    markedKernel_card (A.subgroupOf K) eK hm,?_⟩
  exact (Nat.card_congr eJ.toEquiv).trans automorphismModel_card

theorem source_factor_block_automorphisms_of_solvable
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
    Nonempty (MulAut K ≃* AutomorphismModel) ∧
      Nonempty (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K) ≃*
        Multiplicative (BinaryPermutation.Deleted (Fin 6))) ∧
      IsElementaryAbelian 2 (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K)) ∧
      Nat.card (fixingSubgroup (MulAut K) (A.subgroupOf K : Set K))=32 ∧
      Nat.card (MulAut K)=23040 := by
  intro N Y K
  obtain ⟨hAK,qA,eK,heA,hA⟩ := source_factor_block_split_model_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hm : (A.subgroupOf K).map eK.toMonoidHom=translations := hA
  let eJ := markedAutomorphismEquiv eK natural_block_normalizer
  refine ⟨⟨eJ⟩,⟨markedKernelEquiv (A.subgroupOf K) eK hm⟩,
    markedKernel_elementary (A.subgroupOf K) eK hm,
    markedKernel_card (A.subgroupOf K) eK hm,?_⟩
  exact (Nat.card_congr eJ.toEquiv).trans automorphismModel_card

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
