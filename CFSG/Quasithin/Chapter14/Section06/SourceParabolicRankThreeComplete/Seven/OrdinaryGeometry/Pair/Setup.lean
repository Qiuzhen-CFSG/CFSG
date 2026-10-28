module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup

/-!
# The genuine source inputs for seven-letter pair recognition

The unchanged generated group and recomputed first residual form the original
Goldschmidt triple. The first residual moves the plane, while the actual second
parabolic lies in H and hence centralizes the original order-two point Z.
The literal normalizer and centralizer descriptions of M and Mc are retained.
No partition, coordinate choice or point-stabilizer equality is assumed.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
variable {G : Type*} [Group G] [Finite G]

noncomputable def firstParabolic (T : Sylow 2 G) (M Mc I H2 : Subgroup G) : Subgroup G :=
  firstResidual T M Mc I H2 ⊔ ((T : Subgroup G) ⊓ sourceGeneratedParabolic T M Mc I H2)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))

include hG hempty hM hunique hmany hcard e hab H hH d hI

theorem source_localData :
    LocalData (sourceGeneratedParabolic T M Mc I d.H2)
      (firstParabolic T M Mc I d.H2) (sourceSecondParabolic T I d.H2)
      (localModule T M) (centralInvolutions T) M Mc := by
  let J := sourceGeneratedParabolic T M Mc I d.H2
  let Q := sourceSecondParabolic T I d.H2
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hJ,hS,hgen,hQH2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal
    ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
    ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput
    I d.H2 hI hout d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  have hH2H : d.H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H d.mem_span))).mp
      (d.le_quotient_centralizer hx)).1
  have hQH : Q ≤ H := hQH2.trans hH2H
  have hSQ : (T : Subgroup G) ⊓ J ≤ Q := by
    change (T : Subgroup G) ⊓ J = (T : Subgroup G) ⊓ I at hS
    rw [hS]
    exact le_sup_right
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    d.u d.mem_span d.index d.moves_core d.product_moves_core
  have hsecond := suitable_second_parabolic_data h d.u d.mem_span d.H2 ((T : Subgroup G) ⊓ I)
    (le_inf inf_le_left hI.1.2.1) hS0 hi.1 hi.2.2.2.1
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model hlocal
  have houtJ := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d J hJ
  have hfirst : firstParabolic T M Mc I d.H2 ≤ M :=
    sup_le (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))
      (inf_le_left.trans hM.1.2)
  refine ⟨sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right,
    le_sup_right, ?_, hcard,
    plane_centralInvolutions_card T M hM.1.2 hcard e,
    le_conjugateSpanBy _ _, hfirst,
    InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1,
    ?_, ?_, ?_⟩
  · exact source_parabolic_goldschmidtTriple_of_escape
      hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
      d.moves_core d.product_moves_core d.local_normalizer hlocal
      J Q hJ hSQ hQH hsecond.2.1 houtJ hgen
  · exact (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact hQH.trans
      (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).2
  · refine ⟨firstResidual T M Mc I d.H2, le_sup_left, isPPerfect_embedded_pResidual 2 _, ?_⟩
    exact source_parabolic_plane_moved hG T hempty hM hunique hmany hcard e hab
      H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
      d.local_normalizer hlocal J hJ.1 houtJ

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
