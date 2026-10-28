module
public import Theory.GroupAction.NormalizerFixer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockAutomorphisms
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockNormalizer

/-!
# The possible enlargement of the original elementary subgroup

The original centralizer of A acts faithfully on the source A6-block K and
lands in the pointwise A-fixer in Aut(K). That fixer is elementary abelian of
order 32, so C_G(A) has the same elementary structure and order at most 32.
Since A has order 16, a strict enlargement has order exactly 32.

This supplies the centralizer-size step at the start of Aschbacher–Smith
14.3.20, using the original 14.3.19 block and its normalizer. It does not assert
that the strict-enlargement case is impossible.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem source_factor_centralizer_elementary_of_solvable
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
    IsElementaryAbelian 2 (centralizer (A:Set G)) ∧
      Nat.card (centralizer (A:Set G))≤32 ∧
      (A<centralizer (A:Set G)→Nat.card (centralizer (A:Set G))=32) := by
  let N:=F.H⊓normalizer (A:Set G)
  let Y:=(pResidual 2 N).map N.subtype
  let K:=sourceResidual M Mc⊔Y
  let C:=centralizer (A:Set G)
  obtain ⟨_,_,hEA,hcardE,_⟩ := source_factor_block_automorphisms_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  let := hEA
  have hfaith:Function.Injective K.normalizerMonoidHom :=
    source_factor_block_normalizer_faithful_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hnorm:normalizer (A:Set G)=normalizer (K:Set G) :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  have hCN:C≤normalizer (K:Set G) := by
    rw [←hnorm]
    exact _root_.centralizer_le_normalizer A
  let f:=normalizerFixerHom K A C hCN le_rfl
  have hf:Function.Injective f := normalizerFixerHom_injective K A C hCN le_rfl hfaith
  have hEA':IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective f hf
  have hcardC:Nat.card C≤32 := (Nat.card_le_card_of_injective f hf).trans_eq hcardE
  refine ⟨hEA',hcardC,?_⟩
  intro hlt
  have hlarge:16<Nat.card C := by
    by_contra hbad
    have heq:A=C := eq_of_le_of_card_ge hlt.le (by rw [hAc];omega)
    exact hlt.ne heq
  have hdvd:16∣Nat.card C := hAc ▸ card_dvd_of_le hlt.le
  obtain ⟨m,hm⟩ := hdvd
  change Nat.card C = 32
  omega

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
