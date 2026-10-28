module
public import CFSG.Quasithin.Chapter14.Section02.ProperCommutator
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Characteristic-normalizer control for the proper residual core

For S of index two in the original T, both Y and S are normalized by T.
Thus R=O₂(YS) is normalized by YT. The original plane lies in R, so R is
nontrivial. Uniqueness of M above YT puts every normalizer of a nontrivial
characteristic subgroup of R in M. This is the actual control hypothesis
used by the final C.1.29 application, with the original R and M.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_proper_residual_core_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2) :
    let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
    localModule T M ≤ R ∧ R ≠ ⊥ ∧
      sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      R.characteristicNormalizerClosure ≤ M := by
  let Y := sourceResidual M Mc
  let B := Y ⊔ S
  let R := B.pCoreIn 2
  change localModule T M ≤ R ∧ R ≠ ⊥ ∧ _ ∧ _
  have hYM : Y ≤ M := sourceResidual_le _ _
  have hBM : B ≤ M := sup_le hYM (hST.trans hM.1.2)
  have hVY : localModule T M ≤ Y :=
    (source_plane_module_residual_commutator hG T hempty hM hu hmany hcard e).2
  have hVR : localModule T M ≤ R := le_pCoreIn_of_normalizes
    (InitialSource.localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩).isPGroup
    (hVY.trans le_sup_left) (hBM.trans (le_normalizer_conjugateSpanBy _ _))
  have hRne : R ≠ ⊥ := by
    intro he
    have hv : localModule T M = ⊥ := le_bot_iff.mp (he ▸ hVR)
    rw [hv,card_bot] at hcard
    omega
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hi)
  have hTN : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (le_inf hTY hTS).trans (normalizer_inf_normalizer_le_normalizer_sup Y S)
  have hYN : Y ≤ normalizer (B : Set G) := le_sup_left.trans B.le_normalizer
  have hNR : Y ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (sup_le hYN hTN).trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  refine ⟨hVR,hRne,hNR,?_⟩
  apply characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
    (J := Y ⊔ (T : Subgroup G)) _ (isPGroup_pCoreIn 2 B) hNR
  intro N hN hJN
  obtain ⟨_,_,_,_,_,_,huniq,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  exact Set.mem_singleton_iff.mp (huniq ▸ ⟨hN,hJN⟩)
end CFSG.Quasithin.Chapter14.Section02
