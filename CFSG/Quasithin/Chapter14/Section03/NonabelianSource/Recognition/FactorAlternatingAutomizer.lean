module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorGeneratedResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorParabolicCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersParabolic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorPointResidualAutomizer
public import Theory.GroupAction.BinaryA4Pair.NaturalActors

/-!
# The actual alternating-six action in the elementary-factor branch

The two original normalizers induce symmetric-four groups on A. Their
residuals share the same Sylow action; the parabolic cubic is fixed-point
free, while the point-normalizer residual fixes precisely the original
point. These marks determine the alternating-six natural action on A.
The group equivalence and the module equivalence are constructed together,
so the literal conjugation action intertwines with the six-letter module.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(4), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_alternating_natural_action_of_full_orthogonal
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
    ∃hKA:K≤normalizer (A:Set G),
      ∃ (eA : (A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6))
        (qA : A ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
        ∀ (a : (A.normalizerMonoidHom.comp (inclusion hKA)).range) (v : A),
          (qA (a.val v)).toAdd =
            BinaryPermutation.naturalRepresentation (Fin 6) (eA a).val (qA v).toAdd := by
  intro N Y K
  let I:=F.I₂ (sourceResidual M Mc)
  let R:=I.pCoreIn 2
  let J:=R⊔Y
  let S:=R⊔F.U
  have hIA:I≤normalizer (A:Set G) := le_sup_left.trans hAN
  obtain ⟨_,⟨eI⟩⟩ := factor_parabolic_symmetric_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hIA
  obtain ⟨hJA,_,⟨eJ⟩⟩ := factor_point_residual_symmetric_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN
  obtain ⟨_,hUY,hfixed⟩ := factor_point_residual_fixed_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hSI:S≤I := sup_le (pCoreIn_le 2 _) (le_conjugateSpanBy _ _)
  have hSJ:S≤J := sup_le le_sup_left (hUY.trans le_sup_right)
  have hS:Nat.card (A.normalizerMonoidHom.comp (inclusion (hSI.trans hIA))).range=8 :=
    (factor_join_dihedral_automizer_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 _).1
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hUQ:F.U≤F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hTH:(T:Subgroup G)≤F.H := F.invariant 1
  have hQT:F.H.pCoreIn 2≤(T:Subgroup G) := by
    have hh:=pCoreIn_le_sylow F.H (T.subtype hTH)
    change F.H.pCoreIn 2≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hpS:IsPGroup 2 S := T.isPGroup'.to_le (sup_le hRT (hUQ.trans hQT))
  have hL:sourceResidual M Mc=(pResidual 2 I).map I.subtype :=
    (parabolic_residual_core_structure_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1.symm
  have hY:Y=(pResidual 2 J).map J.subtype :=
    (factor_generated_residual_geometry_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1.symm
  obtain ⟨_,_,t,ht,ht3,_,htfree⟩ := factor_parabolic_cubic_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hAc hIA
  have hfixcard:Nat.card (A⊓centralizer (Y:Set G):Subgroup G)=2 := by
    rw [hfixed]
    simpa using F.card 1 (by decide)
  exact BinaryA4Pair.natural_recognition_of_normalizer_actors A I J S (sourceResidual M Mc) Y hAc
    hIA hJA hSI hSJ eI eJ hS hpS hL hY ⟨t,ht,ht3,htfree⟩ hfixcard
theorem factor_alternating_automizer_of_full_orthogonal
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
    ∃hKA:K≤normalizer (A:Set G),
      Nonempty ((A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hKA,eA,qA,hqA⟩ := factor_alternating_natural_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN
  exact ⟨hKA,⟨eA⟩⟩

theorem source_factor_alternating_natural_action_of_solvable
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
    ∃hKA:K≤normalizer (A:Set G),
      ∃ (eA : (A.normalizerMonoidHom.comp (inclusion hKA)).range ≃* alternatingGroup (Fin 6))
        (qA : A ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
        ∀ (a : (A.normalizerMonoidHom.comp (inclusion hKA)).range) (v : A),
          (qA (a.val v)).toAdd =
            BinaryPermutation.naturalRepresentation (Fin 6) (eA a).val (qA v).toAdd := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨C,D,hCR,hDR,hVC,hVD,hEC,hED,hCc,hDc,hCDi,hCD,hRc,hCN,hDN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  let := hEC
  let := hED
  rcases hmax A inferInstance hAR with hac|had
  · have heq:A=C := eq_of_le_of_card_ge hac (by rw [hAc,hCc])
    exact factor_alternating_natural_action_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A D hAR hDR hVA hAc hc8 (by simpa [heq] using hCD) hRc hAN
  · have heq:A=D := eq_of_le_of_card_ge had (by rw [hAc,hDc])
    exact factor_alternating_natural_action_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A C hAR hCR hVA hAc hc8 (by simpa [heq,sup_comm] using hCD) hRc hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
