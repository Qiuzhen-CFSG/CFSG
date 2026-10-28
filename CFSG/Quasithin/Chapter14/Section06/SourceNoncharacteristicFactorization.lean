module
public import CFSG.Quasithin.Chapter14.Section06.SourceOrdinaryComponentPrimeBound
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponentNormality
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThreeRank
public import CFSG.Quasithin.ChapterE.Section02.Structure.SmallNormalRank.LinearNine

/-!
# The non-characteristic-two source factorization in 14.6.9

The minimal outside choice either gives the literal residual factorizations
from 14.6.6, or is the marked minimal parabolic. In the latter case its
ordinary component receives the original 1.1.5 marking, and rank four
forces that same generating component to be normal. The marked E.2.2
list is then exhausted: the normal degree-three, field-nine and binary
rows force quotient two-rank at most three, while the odd prime-field
linear-two row has no elementary normal Sylow image of rank four.
The literal span image in the actual parabolic quotient supplies the
contradiction throughout. No equality of the parabolic core and O_2 is
assumed.

Source: Aschbacher--Smith 14.6.9, printed pp.1027--1028.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
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
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- Under the original rank-four hypothesis the non-characteristic-two
minimal outside choice satisfies both literal residual factorizations. -/
theorem source_noncharacteristic_factorization
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) (hF : generalizedFitting I ≠ pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_ordinary_component_lists_or_factorization hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hF hI with hm | hf
  · obtain ⟨S,z,hS,hz,h115,hP,hmax,K,hK,hgen,hcomm,hout,hmodel,⟨eqv⟩,hm⟩ := hm
    exfalso
    have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI.1.1 S hS).2.2
    have hs : ¬ Group.IsSolvable I := by
      intro hs
      let := hs
      apply hF
      rw [generalizedFitting_eq_fitting_of_solvable I,Fitting_eq_pcore I 2 hodd]
    let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
    let W := U.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))
    have hfour : 4 ≤ primeRank 2 W :=
      (source_parabolic_quotient_elementary_rank_four hG T hempty hM hunique hmany
        hcard e hab H hH u hu I hI.1 S hS hF hrank hP).2.2.2
    have hstar : 4 ≤ primeRank 2 (I ⧸ ChapterB.minimalParabolicCore S hP) :=
      hfour.trans (primeRank_subgroup_le 2 W)
    let : K.Normal := source_rank_four_component_normal hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI.1 S hS hF hrank hP hmax K hK.isCComponent hgen
    rcases hm with hm | hm | hm
    · rcases hm with hm | hm | hm | ⟨p,hp,hm⟩
      · have hbound := ChapterE.Structure.source_star_odd_degree_three_rank_le_three
          S hP hs K hK.isCComponent hgen (by decide : Nat.Prime 3) (by decide : Odd 3)
          (Or.inl (hm.of_mulEquiv eqv.symm))
        omega
      · have hbound := ChapterE.Structure.source_star_odd_degree_three_rank_le_three
          S hP hs K hK.isCComponent hgen (by decide : Nat.Prime 3) (by decide : Odd 3)
          (Or.inr (hm.of_mulEquiv eqv.symm))
        omega
      · have hbound := ChapterE.Structure.source_ordinary_linear_nine_rank_le_three
          S hP hs K hK hgen hm
        omega
      · obtain ⟨ho,hpguard⟩ := source_parabolic_ordinary_prime_guard hG T hempty hM
          hunique hmany hcard e hab H hH u hu I hI.1.1 S hS hP hmax hF K hK hgen
          eqv hp hm
        let : Fact p.Prime := ⟨hp.1⟩
        obtain ⟨F,hField,hfin,hcardF,⟨eF⟩⟩ := hm.of_mulEquiv eqv.symm
        exact source_parabolic_odd_prime_exclusion hG T hempty hM hunique hmany hcard e
          hab H hH u hu I hI.1 S hS hF hrank hP K hK.isCComponent hgen
          ho hcardF hpguard eF
    · have hbound := ChapterE.Structure.source_star_small_binary_rank_le_three
        S hP hs K hK.isCComponent hgen (Or.inl (hm.of_mulEquiv eqv.symm))
      omega
    · obtain ⟨eD⟩ := hm
      have hbound := ChapterE.Structure.source_star_small_binary_rank_le_three
        S hP hs K hK.isCComponent hgen (Or.inr ⟨eqv.symm.trans eD⟩)
      omega
  · exact hf

end CFSG.Quasithin.Chapter14.Section06
