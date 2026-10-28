module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Exceptional.Geometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The original exceptional A₇ branch of 14.6.10(5)

Retain the original second-parabolic data d, preferred IStar choice I,
point Z = centralInvolutions T and plane V = localModule T M. The actual
component is C = O²(I₀), and the full generated plane span lies in its
block commutator module. The exceptional-block action on this module is
the faithful four-dimensional binary action of C/O₂(C).

The source Sylow intersection contains a Sylow subgroup of C and the
two-core of the second parabolic J. Hence O₂(J) normalizes V. The
original H centralizes Z, and J cannot normalize V because N_G(V) = M.
These facts discharge every premise of the intrinsic span calculation:
the literal J-span is elementary abelian of order eight and rank three.

The final export discharges Seven.Source's exceptional input. This module
does not import that assembly, so its owner can import the contract here.
Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Exceptional
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original exceptional second-parabolic span has order eight and rank three. -/
theorem source_span
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G))
    (hC : ChapterC.IsExceptionalA7Block (sourceGeneratedComponent T M Mc I d.H2)) :
    IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) ∧
      Nat.card (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) = 3 := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let C := sourceGeneratedComponent T M Mc I d.H2
  let J := sourceSecondParabolic T I d.H2
  let S := (T : Subgroup G) ⊓ I
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  obtain ⟨hI0,hS,_,hJH,_⟩ := generated_choice hG T hempty hM hunique hmany hcard e hab
    H hH d I hI hpreferred
  have hspan := generated_span_le_module hG T hempty hM hunique hmany hcard e hab
    H hH d I hI
  have hVW : localModule T M ≤ (ChapterC.blockU C).map C.subtype :=
    (le_conjugateSpanBy _ I0).trans hspan
  have hCI : C ≤ I0 := map_subtype_le _
  have hIC : I0 ≤ normalizer (C : Set G) := I0.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I0 (pResidual 2 I0))
  have hJI : J ≤ I0 := le_sup_right
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I0 hI0.1).1
  have hCN : (C.subgroupOf I0).Normal := normal_subgroupOf_of_le_normalizer hIC
  obtain ⟨P,hPC⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hCI
    hCN.isSubnormal
  have hPS : (P : Subgroup C).map C.subtype ≤ S := by
    exact hPC.le.trans (inf_le_left.trans hS.le)
  have hSJ : S ≤ J := le_sup_right
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH d.u d.mem_span d.index d.moves_core d.product_moves_core
    d.local_normalizer hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    d.u d.mem_span d.index d.moves_core d.product_moves_core
  obtain ⟨hSylJ,⟨eJ⟩,_⟩ := suitable_second_parabolic_data h d.u d.mem_span d.H2 S
    (le_inf inf_le_left hI.1.2.1) hS0 hi.1 hi.2.2.2.1
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model hlocal
  obtain ⟨PJ,hPJ⟩ := hSylJ
  have hcoreV : J.pCoreIn 2 ≤ normalizer (localModule T M : Set G) :=
    ((pCoreIn_le_sylow J PJ).trans hPJ.le).trans
      (inf_le_left.trans (hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)))
  have hJZ : J ≤ centralizer (centralInvolutions T : Set G) :=
    hJH.trans (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).2
  have hJM : ¬ J ≤ M := by
    intro hj
    apply hI0.1.2.2.2
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hj
  have hm : ¬ J ≤ normalizer (localModule T M : Set G) := by
    rwa [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
  exact span_rank_three C J (localModule T M) (centralInvolutions T) hC
    (hJI.trans hIC) hVW (le_conjugateSpanBy _ _) hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e) hcoreV hJZ P
    (hPS.trans hSJ) eJ hm

/-- The exact exceptional branch contract, with no extra geometric premises. -/
theorem source_rank_input : ExceptionalRankInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI hpreferred hC
  exact (source_span hG T hempty hM hunique hmany hcard e hab H hH d I hI hpreferred hC).2.2

end CFSG.Quasithin.Chapter14.Section06.Seven.Exceptional
