module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAlternatingAutomizer
public import Theory.GroupTheory.PCoreActionSplitting
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The alternating-six quotient of the original generated group

The action on the selected elementary factor has two-group kernel because
its full ambient centralizer is a two-group. Its alternating-six image has
trivial two-core, so the literal action kernel is precisely O₂(K). The
quotient equivalence uses this same conjugation homomorphism. The final
source wrapper selects the factor and discharges every geometric input
from the original solvable terminal branch.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(4), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G:Type*} [Group G] [Finite G]

private theorem action_six_core_quotient
    {G : Type*} [Group G] [Finite G] (A K:Subgroup G)
    (hKA:K≤normalizer (A:Set G))
    (hc:IsPGroup 2 (centralizer (A:Set G)))
    (e:(A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6)) :
    K.pCoreIn 2=K⊓centralizer (A:Set G) ∧ Nonempty ((K⧸pCore 2 K)≃*alternatingGroup (Fin 6)) := by
  let f:=A.normalizerMonoidHom.comp (inclusion hKA)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup f.range := e.isSimpleGroup
  have hsize:Nat.card f.range=360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcore:pCore 2 f.range=⊥ := by
    rcases (inferInstance:(pCore 2 f.range).Normal).eq_bot_or_eq_top with hh|hh
    · exact hh
    · have hp:IsPGroup 2 (⊤:Subgroup f.range) := hh ▸ pCore_isPGroup
      have hp':IsPGroup 2 f.range := hp.of_equiv Subgroup.topEquiv
      obtain ⟨n,hn⟩:=hp'.exists_card_eq
      have hnodd:Nat.Coprime (2^n) 3 := (by decide:Nat.Coprime 2 3).pow_left n
      rw [←hn,hsize] at hnodd
      norm_num at hnodd
  have hker:f.ker=(centralizer (A:Set G)).subgroupOf K := by
    ext x
    change inclusion hKA x∈A.normalizerMonoidHom.ker ↔ (x:G)∈centralizer (A:Set G)
    rw [normalizerMonoidHom_ker]
    rfl
  have hpker:IsPGroup 2 f.ker := hker.symm ▸ hc.comap_subtype
  have hk:f.ker=pCore 2 K := f.ker_eq_pCore_of_range_core_eq_bot 2 hpker hcore
  constructor
  · change (pCore 2 K).map K.subtype=K⊓centralizer (A:Set G)
    rw [←hk,hker,subgroupOf_map_subtype,inf_comm]
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans e)⟩
theorem factor_core_quotient_of_full_orthogonal
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
    (A B:Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hBR:B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAB:A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hRc:Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let K := sourceResidual M Mc⊔Y
    K.pCoreIn 2=K⊓centralizer (A:Set G) ∧
      Nonempty ((K⧸pCore 2 K)≃*alternatingGroup (Fin 6)) := by
  obtain ⟨hKA,⟨eA⟩⟩ := factor_alternating_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN
  have hc := (factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8).2
  exact action_six_core_quotient A _ hKA hc eA

theorem source_factor_core_quotient_of_solvable
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
    K.pCoreIn 2=K⊓centralizer (A:Set G) ∧
      Nonempty ((K⧸pCore 2 K)≃*alternatingGroup (Fin 6)) := by
  obtain ⟨hKA,eA,qA,hqA⟩ := source_factor_alternating_natural_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hc := (factor_global_centralizer_twoGroup_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8).2
  exact action_six_core_quotient A _ hKA hc eA

theorem source_factor_alternating_quotient_of_solvable
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
 :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    ∃ A : Subgroup G, A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧
      Nat.card A=16 ∧ Nat.card (A⊓F.U:Subgroup G)=8 ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G) ∧
      let N := F.H⊓normalizer (A:Set G)
      let Y := (pResidual 2 N).map N.subtype
      let K := sourceResidual M Mc⊔Y
      ∃ hKA:K≤normalizer (A:Set G),
        ∃ (eA : (A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6))
          (qA : A ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
          (∀ (a : (A.normalizerMonoidHom.comp (inclusion hKA)).range) (v : A),
            (qA (a.val v)).toAdd =
              BinaryPermutation.naturalRepresentation (Fin 6) (eA a).val (qA v).toAdd) ∧
          K.pCoreIn 2=K⊓centralizer (A:Set G) ∧
          Nonempty ((K⧸pCore 2 K)≃*alternatingGroup (Fin 6)) := by
  obtain ⟨_,A,hAR,hVA,hEA,hAc,hc8,hAN,_⟩ := source_factor_supplement_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  obtain ⟨hKA,eA,qA,hqA⟩ := source_factor_alternating_natural_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hcore := source_factor_core_quotient_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  exact ⟨A,hAR,hVA,hEA,hAc,hc8,hAN,hKA,eA,qA,hqA,hcore⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
