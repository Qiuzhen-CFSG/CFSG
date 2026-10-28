module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankExclusions
public import CFSG.Quasithin.Chapter14.Section06.SourceOrdinaryComponentPrimeBound
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Paired

/-!
# Normality of the original generating component at rank four

An exchanged component has a binary linear-two, Suzuki, or odd prime-field
linear-two star image by the actual paired-component catalogue. The marked
central line excludes both Bender rows. The small-prime guard and the rank
contradiction exclude the remaining prime-field row. Thus the original
component is normal, before considering its particular small model.

Source: Aschbacher--Smith 14.6.9, printed pp.1027--1028, using E.2.2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Under the original rank-four hypothesis, a generating source component
is normal. This discharges the paired branch without extra model assumptions. -/
theorem source_rank_four_component_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hF : generalizedFitting I ≠ pCore 2 I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hmax : ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I)
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup I) = ⊤) : K.Normal := by
  classical
  by_contra hn
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1 S hS).2.2
  have hs : ¬ Group.IsSolvable I := by
    intro hs
    let := hs
    apply hF
    rw [generalizedFitting_eq_fitting_of_solvable I,Fitting_eq_pcore I 2 hodd]
  have hnB := source_parabolic_bender_exclusion hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1 S hS hP hmax hF K hK hgen
  rcases ChapterE.Structure.source_original_paired_models
    ChapterA.Section02.theoremA_knownSimple (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (Chapter3.sqtk_of_mem_H hG hI.1.1) S hP hs K hK hgen hn with
      ⟨f,hf,hm⟩ | ⟨m,hm,he⟩ | ⟨p,hp,ho,hm⟩
  · exact hnB (.linear f hf hm)
  · exact hnB (.suzuki m hm he)
  · have hparam := source_parabolic_odd_prime_guard hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI.1 S hS hP hmax hF K hK hgen hp ho hm
    obtain ⟨F,hfield,hfin,hcardF,⟨emodel⟩⟩ := hm
    let : Fact p.Prime := ⟨hp⟩
    exact source_parabolic_odd_prime_exclusion hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI S hS hF hrank hP K hK hgen ho hcardF hparam emodel

end CFSG.Quasithin.Chapter14.Section06
