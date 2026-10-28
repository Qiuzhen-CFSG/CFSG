module
public import CFSG.Quasithin.Chapter14.Section02.ProperSylow
public import Theory.GroupTheory.MaximalTwoLocalCore

/-!
# Core-centralizer control in the proper-index completion

The chosen S is Sylow in a maximal local M₁ containing the completion.
Consequently O₂(M₁) lies in O₂(G₀). The full centralizer of O₂(M₁) lies
in M₁ by maximality, and T intersects M₁ exactly in S. This proves the
literal core-centralizer bound in the displayed chain (*) of 14.2.15.
The source consumer reuses the genuine Sylow reduction with its earlier
14.2.10 placement premise.

Source: Aschbacher--Smith 14.2.15, printed p.985.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A completion containing a Sylow subgroup of a maximal local inherits the
core-centralizer bound needed in original 1.2.11. -/
theorem proper_completion_core_control
    (T : Sylow 2 G) (S X M₁ : Subgroup G)
    (hST : S ≤ (T : Subgroup G)) (hSX : S ≤ X) (hXM : X ≤ M₁)
    (hM : IsMaximalTwoLocal M₁) (hs : Chapter1.IsSylowIn 2 S M₁) :
    (T : Subgroup G) ⊓ X = S ∧
      M₁.pCoreIn 2 ≤ X.pCoreIn 2 ∧
      (T : Subgroup G) ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ S := by
  have hTM : (T : Subgroup G) ⊓ M₁ = S := (Chapter1.isSylowIn_iff.mp hs).2.2 _
    (T.isPGroup'.to_le inf_le_left) (le_inf hST (hSX.trans hXM)) inf_le_right
  have hTX : (T : Subgroup G) ⊓ X = S := le_antisymm
    ((inf_le_inf_left _ hXM).trans_eq hTM) (le_inf hST hSX)
  obtain ⟨P,hP⟩ := hs
  have hQS : M₁.pCoreIn 2 ≤ S := (pCoreIn_le_sylow M₁ P).trans_eq hP
  have hc : M₁.pCoreIn 2 ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 M₁) (hQS.trans hSX)
    (hXM.trans (M₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M₁ (pCore 2 M₁))))
  refine ⟨hTX,hc,?_⟩
  intro t ht
  rw [←hTM]
  exact ⟨ht.1, (maximalTwoLocal_normalizer_core hM) ▸
    (Subgroup.centralizer_le_normalizer _ (centralizer_le hc ht.2))⟩

/-- Literal source completion with the original selected K₁, Y and S. -/
theorem source_proper_completion_core_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    (T : Subgroup G) ⊓ X = S ∧
      (T : Subgroup G) ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ S := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  obtain ⟨M₁,hM₁,hXM₁⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot X hcore
  obtain ⟨_,_,_,_,_,_,hunique,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hHMc : H ≤ Mc := ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).2).trans (InitialSource.centralizer_le_partner T hu)
  have hs := proper_completion_sylow_in_maximal T M Mc H (sourceResidual M Mc) K S M₁
    hST hi (hH.1.1.2.trans hHMc) hHMc hH.1.2 hunique hN hplacement hM₁
    ((le_sup_left.trans le_sup_left).trans hXM₁)
    ((le_sup_right.trans le_sup_left).trans hXM₁) (le_sup_right.trans hXM₁)
  obtain ⟨he,_,hc⟩ := proper_completion_core_control T S X M₁ hST le_sup_right hXM₁ hM₁ hs
  exact ⟨he,hc⟩
end CFSG.Quasithin.Chapter14.Section02
