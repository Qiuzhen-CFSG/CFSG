module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.ExceptionalTripleSix

/-!
# The A₆ central-quotient branch of original 14.6.10(5)

The original source supplies the actual C.2.7 component and odd-index
radical. Whole-core reconstruction on that same component gives either
the natural A₆ block or the exceptional triple cover. The source invariant
subgroup dichotomy excludes the latter. The completed natural-six argument
then computes rank three, including the rank-five permutation-core case.

Only the independently owned A₆ whole-core reconstruction theorem remains
explicit. No blockhood is inferred from a star-image tag.
Source: Aschbacher--Smith, original 14.6.10(5), printed pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The reconstructed central-cover alternatives give the natural block
on the literal generated component; the exceptional source branch is impossible. -/
theorem source_second_parabolic_alternating_block_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (he : Nonempty (((sourceGeneratedComponent T M Mc I d.H2) ⧸
      centralPreimage (pCore 2 (sourceGeneratedComponent T M Mc I d.H2))) ≃*
        alternatingGroup (Fin 6))) :
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 6 := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hi,hr,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  rcases alternatingSix_or_exceptional_from_c27 ha hi hr he.some with hb | hb
  · exact hb
  · exact (source_generated_parabolic_not_exceptionalTripleSix
      hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
      d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
      d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
      d.core_index d.module_rank hb).elim

/-- The A₆ branch is complete once the independent whole-core reconstruction
is supplied; escape, Sylow placement and exceptional-cover exclusion are discharged. -/
theorem source_second_parabolic_a6_rank_three_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple) :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ centralPreimage (pCore 2 C)) ≃*
        alternatingGroup (Fin 6))) := by
  intro H hH d I hI hpreferred he
  exact source_second_parabolic_rank_three_of_alternating_block
    hG T hempty hM hunique hmany hcard e hab H hH d I hI hpreferred
    (source_second_parabolic_alternating_block_of_reconstruction
      hG T hempty hM hunique hmany hcard e hab ha H hH d I hI he)

end CFSG.Quasithin.Chapter14.Section06
