module
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SylowConclusion

/-!
# The Sylow reduction for the proper-index large amalgam

Every two-overgroup of an index-two subgroup S of the original Sylow lies
in N_G(S), hence in Mc once the central-omega normalizer is controlled.
A strict overgroup has full Sylow order. Source 14.2.10 then makes Mc its
unique maximal local overgroup together with K₁, contrary to the distinct
unique maximal overgroup of YT. Thus S is Sylow in any proposed completion
with nontrivial two-core. The final theorem applies this argument to the
literal K₁, Y and S; only the separately produced 14.2.10 placement and
central-omega normalizer conclusions remain explicit.

Source: Aschbacher--Smith 14.2.15, first paragraph, printed p.985.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The index-two source argument makes S Sylow in every maximal local
containing the proposed completion. -/
theorem proper_completion_sylow_in_maximal
    (T : Sylow 2 G) (M Mc H Y K S M₁ : Subgroup G)
    (hST : S ≤ (T : Subgroup G)) (hi : S.relIndex (T : Subgroup G) = 2)
    (hTMc : (T : Subgroup G) ≤ Mc) (hHMc : H ≤ Mc) (hout : ¬ H ≤ M)
    (hunique : maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M})
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hM₁ : IsMaximalTwoLocal M₁) (hKM₁ : K ≤ M₁) (hYM₁ : Y ≤ M₁)
    (hSM₁ : S ≤ M₁) : Chapter1.IsSylowIn 2 S M₁ := by
  have hSp : IsPGroup 2 S := T.isPGroup'.to_le hST
  obtain ⟨P,hSP⟩ := (hSp.comap_subtype (K := M₁)).exists_le_sylow
  let R := (P : Subgroup M₁).map M₁.subtype
  have hSR : S ≤ R := by
    rw [← map_subgroupOf_eq_of_le hSM₁]
    exact map_mono hSP
  have hRM₁ : R ≤ M₁ := map_subtype_le _
  have hN' : normalizer (S : Set G) ≤ Mc := by
    refine le_trans ?_ hN
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
    exact congrArg omegaOneCenterAmbient (mem_normalizer_iff_map_conj_eq.mp hg)
  have hRMc : R ≤ Mc := OutsideStructure.two_overgroup_le_of_index_two T S Mc R hST hi
    hN' (P.isPGroup'.map _) hSR
  refine ⟨P,?_⟩
  change R = S
  by_contra hne
  obtain ⟨U,hU⟩ := OutsideStructure.sylow_of_strict_overgroup T S R hST hi
    (P.isPGroup'.map _) (lt_of_le_of_ne hSR (Ne.symm hne))
  have hUMc : (U : Subgroup G) ≤ Mc := hU ▸ hRMc
  have hmapU : (U.subtype hUMc : Subgroup Mc).map Mc.subtype = R := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hUMc,hU]
  have hu : maximalTwoLocalOvergroups (K ⊔ R) = {Mc} := by
    simpa only [hmapU] using hplacement (U.subtype hUMc) (hmapU.symm ▸ hSR)
  have he : M₁ = Mc := Set.mem_singleton_iff.mp
    (hu ▸ (show M₁ ∈ maximalTwoLocalOvergroups (K ⊔ R) from ⟨hM₁,sup_le hKM₁ hRM₁⟩))
  have he' : Mc = M := Set.mem_singleton_iff.mp
    (hunique ▸ (show Mc ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) from
      ⟨he ▸ hM₁,sup_le (he ▸ hYM₁) hTMc⟩))
  exact hout (he' ▸ hHMc)

/-- Literal 14.2.15 Sylow reduction: the independent inputs are the
normalizer conclusion and the strengthened placement in 14.2.10. -/
theorem source_proper_completion_sylow
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
    Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  obtain ⟨M₁,hM₁,hXM₁⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot X hcore
  obtain ⟨_,_,_,_,_,_,hunique,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hHMc : H ≤ Mc := ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).2).trans (InitialSource.centralizer_le_partner T hu)
  have hs := proper_completion_sylow_in_maximal T M Mc H (sourceResidual M Mc) K S M₁
    hST hi (hH.1.1.2.trans hHMc) hHMc hH.1.2 hunique hN hplacement hM₁
    ((le_sup_left.trans le_sup_left).trans hXM₁)
    ((le_sup_right.trans le_sup_left).trans hXM₁) (le_sup_right.trans hXM₁)
  exact hs.restrict le_sup_right hXM₁
end CFSG.Quasithin.Chapter14.Section02
