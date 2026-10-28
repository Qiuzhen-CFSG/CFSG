module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.AmbientAction
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.DeletedElementaryMaxima
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugateCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorCentralizerElementary
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockSupplement
/-!
# The full factor-block normalizer under strict centralizer enlargement

If the centralizer of the selected elementary subgroup A is larger than A,
it has order 32. A conjugate of this centralizer normalizes A and escapes the
original centralizer. The deleted-module elementary-subgroup theorem forces
an odd permutation coordinate in the normalizer action. Inner automorphisms
already supply all even coordinates, so the action realizes every
automorphism of the natural A6 block.

Consequently the normalizer has order 23040, its index over the block is four,
its two-core is precisely the centralizer of A, and the actual supplement
O2(H) intersect C_G(U) is dihedral of order eight.

Source: Aschbacher–Smith 14.3.20, first paragraph, using 14.3.19(6),(10).
The later involution-centralizer contradiction of 14.3.20 is separate.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SixNaturalSplit
variable {G:Type*} [Group G] [Finite G]

theorem source_factor_full_automorphism_of_strict_centralizer
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
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    let N:=F.H⊓normalizer (A:Set G)
    let Y:=(pResidual 2 N).map N.subtype
    let K:=sourceResidual M Mc⊔Y
    Function.Bijective K.normalizerMonoidHom ∧
      Nat.card (normalizer (A:Set G))=23040 ∧
      K.relIndex (normalizer (A:Set G))=4 := by
  intro N Y K
  let C:=centralizer (A:Set G)
  obtain ⟨hEA,_,hCc'⟩:=source_factor_centralizer_elementary_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  let :=hEA
  have hCc:Nat.card C=32 := hCc' hlt
  obtain ⟨_,t,ht,hCNt,hneC⟩:=source_factor_conjugate_centralizer_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hnorm:normalizer (A:Set G)=normalizer (K:Set G) :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  have hfaith:Function.Injective K.normalizerMonoidHom :=
    source_factor_block_normalizer_faithful_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  obtain ⟨hAK,qA,eK,_,hA⟩:=source_factor_block_split_model_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  let :IsElementaryAbelian 2 (conjugate C t) :=
    IsElementaryAbelian.map (MulAut.conj t⁻¹).toMonoidHom
  have htcard:Nat.card (conjugate C t)=32 :=
    (card_map_of_injective (MulAut.conj t⁻¹).injective).trans hCc
  have hsurj:Function.Surjective K.normalizerMonoidHom :=
    ambientAction_surjective_of_large_elementary K A hAK eK hA natural_block_normalizer hfaith
      (hnorm ▸ _root_.centralizer_le_normalizer A) hCc (conjugate C t)
      (hnorm ▸ hCNt) (by rw [htcard]) hneC
      (fun B hB he hc=>by let :=hB; exact deleted_elementary_le_kernel B he hc)
  have hNc:Nat.card (normalizer (K:Set G))=23040 := by
    rw [Nat.card_congr (MulEquiv.ofBijective K.normalizerMonoidHom ⟨hfaith,hsurj⟩).toEquiv]
    rw [Nat.card_congr (markedAutomorphismEquiv eK natural_block_normalizer).toEquiv]
    exact automorphismModel_card
  have hKc:Nat.card K=5760 := (source_factor_block_core_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2.2.2.1
  refine ⟨⟨hfaith,hsurj⟩,hnorm ▸ hNc,?_⟩
  rw [hnorm]
  have hh:=relIndex_mul_card_of_le K.le_normalizer
  rw [hKc,hNc] at hh
  omega


theorem source_factor_normalizer_core_of_strict_centralizer
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
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    (normalizer (A:Set G)).pCoreIn 2=centralizer (A:Set G) := by
  let N:=F.H⊓normalizer (A:Set G)
  let Y:=(pResidual 2 N).map N.subtype
  let K:=sourceResidual M Mc⊔Y
  let C:=centralizer (A:Set G)
  let NK:=normalizer (K:Set G)
  have hb:= (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt).1
  obtain ⟨hAK,qA,eK,_,hA⟩:=source_factor_block_split_model_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hnorm:normalizer (A:Set G)=NK :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  have hCN:C≤NK := hnorm ▸ _root_.centralizer_le_normalizer A
  let f: NK→*AutomorphismModel := ambientAction K eK natural_block_normalizer
  have hf:Function.Surjective f := ambientAction_surjective K eK natural_block_normalizer hb.2
  let q: NK→*Equiv.Perm (Fin 6) := SemidirectProduct.rightHom.comp f
  have hq:Function.Surjective q := SemidirectProduct.rightHom_surjective.comp hf
  have hker:q.ker=C.subgroupOf NK := by
    ext x
    exact ambientAction_right_eq_one K A hAK eK hA natural_block_normalizer x
  have hp:IsPGroup 2 C :=
    (source_factor_centralizer_elementary_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).1.isPGroup
  have hpk:IsPGroup 2 q.ker := hker.symm ▸ hp.comap_subtype
  have hcore:=q.comap_pCore_of_ker_isPGroup hq hpk
  rw [alternatingGroup.SevenComponent.symmetric_six_twoCore,MonoidHom.comap_bot,hker] at hcore
  rw [hnorm]
  change (pCore 2 NK).map NK.subtype=C
  rw [←hcore,map_subgroupOf_eq_of_le hCN]

/-- Strict enlargement forces the actual source supplement to be dihedral. -/
theorem source_factor_supplement_dihedral_of_strict_centralizer
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
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    Nonempty ((F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G) ≃* DihedralGroup 4) := by
  let N := F.H ⊓ normalizer (A : Set G)
  let K := sourceResidual M Mc ⊔ (pResidual 2 N).map N.subtype
  have hi := (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt).2.2
  have hn := (source_factor_block_normalizer_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  have hi' : K.relIndex (normalizer (K : Set G)) = 4 :=
    (congrArg (fun B : Subgroup G => K.relIndex B) hn).symm.trans hi
  exact (source_factor_block_supplement_dihedral_iff_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).mpr
      ⟨hi', hlt⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
