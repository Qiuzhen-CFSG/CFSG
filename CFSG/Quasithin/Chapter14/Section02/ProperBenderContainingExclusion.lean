module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender

/-!
# Early exclusion of the Bender containing models

In the original proper completion, the selected local component K is
properly contained in the canonical residual L. Restricting the original
full Sylow to the completion lets A.3.12 force K = L whenever L is an
actual binary PSL₂, binary PSU₃, or Suzuki model. The established rank-one
Borel facts supply the solvability of proper Sylow overgroups in all
three families. The model is transported by the actual subgroupOf equivalence.

This eliminates the Bender part of the Lie-type row of 1.1.5 before any
paired three-rank argument or later maximal-local placement is needed.
Source: Aschbacher--Smith 14.2.15, pp.985--986; A.3.12, pp.47--48;
F.1.3(1), pp.259--260; and 1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 14.2.15 excludes every actual Bender containing model,
without a paired-residual or later maximal-local premise. -/
theorem source_proper_completion_bender_exclusion
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
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬ ClassificationModels.IsBenderModel L := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬ ClassificationModels.IsBenderModel L
  intro hmodel
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hne : K ≠ L := fun he =>
    source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
      H hH K S hST hgen hK hSN hcorea hs (he.ge.trans hKC)
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hKP : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_bender_containing_component
    P hKP.1 hL.2 (comap_mono hKL)
    (hmodel.of_mulEquiv (subgroupOfEquivOfLe hL.1))
  apply hne
  have he' := congrArg (Subgroup.map X.subtype) he
  rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at he'

end CFSG.Quasithin.Chapter14.Section02
