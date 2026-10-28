module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section02.SelectedComponentPlacement

/-!
# The three-rank bound on the literal component overlap image

The source places H in Mc. Thus M intersect K has three-rank at most one,
by the original bound on M intersect Mc. Quotienting by a two-group kernel
preserves odd prime rank. Consequently every solvable subgroup of the
marked component quotient invariant under its Sylow normalizer has
three-rank at most one, using 14.6.18 to place its lift in M.

Source: Aschbacher--Smith 14.6.20, printed p.1037, using 14.2.2(1),(4).
Original 14.6.18 remains with qt-e-14625-source; the actual flag-model
applications are supplied by the terminal component-support owner.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G B : Type*} [Group G] [Finite G] [Group B] [Finite B]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
include hG hempty hM hunique hmany hcard e

/-- The image of M intersect K under the actual quotient map has three-rank
at most one; neither normality nor perfectness of K is needed here. -/
theorem source_component_overlap_image_threeRank_le_one
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (q : K →* B) (hk : IsPGroup 2 q.ker) :
    primeRank 3 ((M.subgroupOf K).map q) ≤ 1 := by
  have hu := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
  have hHMc : H ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups H from hu ▸ Set.mem_singleton Mc).2
  have hNK : (M.subgroupOf K).map K.subtype ≤ M ⊓ Mc := by
    rw [subgroupOf_map_subtype]
    exact le_inf inf_le_left (inf_le_right.trans (hKH.trans hHMc))
  have he := primeRank_equiv 3
    ((M.subgroupOf K).equivMapOfInjective K.subtype K.subtype_injective)
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) q hk,he]
  exact (primeRank_mono 3 hNK).trans
    (Section02.source_intersection_threeRank_le_one hG T hempty hM hunique hmany hcard e)

/-- Every invariant solvable model subgroup has three-rank at most one,
after lifting it through the literal component quotient. -/
theorem source_component_invariant_solvable_threeRank_le_one
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ a : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map a.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) →
      J.map a.toMonoidHom = J) : primeRank 3 J ≤ 1 := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hj := source_component_solvable_le_image T M hsolv H hH.1 K hKH hK eK J
    (fun s => hinv _
      (Subgroup.NormalSylowQuotientAction.markedCoreAction_preserves_component_sylow
        2 T K eK P hP s))
  exact (primeRank_mono 3 hj).trans
    (source_component_overlap_image_threeRank_le_one hG T hempty hM hunique hmany hcard e
      H hH K hKH q (hk.symm ▸ pCore_isPGroup))

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
