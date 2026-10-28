module

public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.Chapter14.Section06.SourceMinimalParabolic
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualComponentBender

/-!
# The original central involution in the nonsolvable parabolic quotient

In the non-characteristic-two branch of 14.6.9, the vanishing odd core
forces an ordinary component of I. That component centralizes every
solvable normal subgroup, so the involution supplied by 14.6.7 cannot lie
in the solvable core of the marked minimal parabolic: otherwise the
component would lie in its forbidden involution centralizer Mc.

The actual maximal subgroup I ∩ Mc centralizes the same involution.
Its cyclic line therefore supplies both the surviving point and the
residual centralization required by the E.2.2 Bender-component exclusion.
The hypothesis F*(I) ≠ O₂(I) is retained explicitly.

Source: Aschbacher--Smith 14.6.7 and the last case of 14.6.9,
printed pp.1024,1027--1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem ordinary_component_of_fitting_ne_twoCore
    {I : Subgroup G} (hodd : pPrimeCore 2 I = ⊥)
    (hF : generalizedFitting I ≠ pCore 2 I) :
    ∃ K : Subgroup I, IsComponent I K := by
  by_contra hnone
  have hE : componentLayer I = ⊥ := by
    apply le_bot_iff.mp
    exact sSup_le fun K hK => (hnone ⟨K,hK⟩).elim
  apply hF
  rw [generalizedFitting,hE,sup_bot_eq,Fitting_eq_pcore I 2 hodd]

private theorem nonsolvable_of_fitting_ne_twoCore
    {I : Subgroup G} (hodd : pPrimeCore 2 I = ⊥)
    (hF : generalizedFitting I ≠ pCore 2 I) : ¬ Group.IsSolvable I := by
  obtain ⟨L,hL⟩ := ordinary_component_of_fitting_ne_twoCore hodd hF
  intro hs
  let := hs
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact Group.IsPerfect.not_isSolvable L inferInstance

section Marked
variable
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
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hmax : ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I)
    (hF : generalizedFitting I ≠ pCore 2 I)

include hG hempty hM hunique hmany hcard e hab H hH hu hI hS hmax hF

/-- The involution from the original intersection survives the solvable
minimal-parabolic core and is centralized by the literal marked maximal subgroup. -/
theorem source_parabolic_central_point :
    ∃ z : I, orderOf z = 2 ∧ z ∈ S ∧
      z ∉ ChapterB.minimalParabolicCore S hP ∧
      ChapterB.minimalParabolicMax S hP ≤ centralizer ({z} : Set I) := by
  obtain ⟨⟨z,hz,h115⟩,_,hodd⟩ := source_lemma_14_6_7_initial hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS
  obtain ⟨K,hK⟩ := ordinary_component_of_fitting_ne_twoCore hodd hF
  have hzI : z ∈ I := (map_subtype_le (S : Subgroup I)) h115.mem_sylow
  let zi : I := ⟨z,hzI⟩
  have hzS : zi ∈ S := by
    obtain ⟨a,ha,he⟩ := h115.mem_sylow
    exact (Subtype.ext he : a = zi) ▸ ha
  have hzJ : zi ∉ ChapterB.minimalParabolicCore S hP := by
    intro hzi
    let : Group.IsSolvable (ChapterB.minimalParabolicCore S hP) :=
      ChapterB.minimalParabolic_core_solvable S hP
    have hc := hK.le_centralizer_of_solvable_normal (ChapterB.minimalParabolicCore S hP)
    apply (h115.component_inputs K hK).1
    rintro k ⟨a,ha,rfl⟩
    apply h115.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact congrArg I.subtype (hc ha zi hzi)
  refine ⟨zi,(Subgroup.orderOf_coe zi).symm.trans h115.involution,hzS,hzJ,?_⟩
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  intro b hb
  rw [hmax] at hb
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  exact ((hMc ▸ hb.2) z hz).symm

/-- The actual central line removes either normal or exchanged Bender
components in the non-characteristic-two branch of original 14.6.9. -/
theorem source_parabolic_bender_exclusion
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup I) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)))) : False := by
  obtain ⟨z,hz,hzS,hzJ,hcentral⟩ := source_parabolic_central_point hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS hP hmax hF
  obtain ⟨_,_,hodd⟩ := source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS
  have hs := nonsolvable_of_fitting_ne_twoCore hodd hF
  let V := zpowers z
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hz ▸ pow_orderOf_eq_one z)
  have hVT : V ≤ (S : Subgroup I) := zpowers_le.mpr hzS
  have hMC : ChapterB.minimalParabolicMax S hP ≤ centralizer (V : Set I) := by
    simpa only [V,zpowers_eq_closure,centralizer_closure] using hcentral
  have hVN : (V.subgroupOf (S : Subgroup I)).Normal :=
    normal_subgroupOf_of_le_normalizer (((ChapterB.minimalParabolicMax_spec S hP).2.trans hMC).trans
      (Subgroup.centralizer_le_normalizer _))
  exact ChapterE.Witnesses.PairedBender.source_original_component_bender_residual_exclusion
    ChapterA.Section02.theoremA_knownSimple (Chapter3.sqtk_of_mem_H hG hI.1)
    S hP hs K hK hgen hm V hVT hVN
    (fun hv => hzJ (hv (mem_zpowers z))) ((map_subtype_le _).trans hMC)

end Marked

open scoped Pointwise

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


/-- The non-characteristic-two source branch of 14.6.9 either already
has both required factorizations, or has a generating C-component whose
literal minimal-parabolic quotient image is not a Bender model.
The marked parabolic and component are constructed from the original minimal
outside choice; they are not additional hypotheses. -/
theorem source_noncharacteristic_component_or_factorization
    (I : Subgroup G) (hF : generalizedFitting I ≠ pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
      ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I ∧
      ∃ K : Subgroup I, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        K ⊔ (S : Subgroup I) = ⊤ ∧
        IsComponent (I ⧸ pCore 2 I) (K.map (QuotientGroup.mk' (pCore 2 I))) ∧
        ¬ ClassificationModels.IsBenderModel
          (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)))) ∨
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨⟨S,hS⟩,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1.1
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI.1.1 S hS).2.2
  have hs := nonsolvable_of_fitting_ne_twoCore hodd hF
  rcases source_nonsolvable_component_or_factorization hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hs hI with
    ⟨S,hS,hP,hmax,K,hK,hquasi,hgen,himage⟩ | hf
  · exact Or.inl ⟨S,hS,hP,hmax,K,hK,hquasi,hgen,himage,
      source_parabolic_bender_exclusion hG T hempty hM hunique hmany hcard e hab
        H hH u hu I hI.1.1 S hS hP hmax hF K hK hgen⟩
  · exact Or.inr hf

end CFSG.Quasithin.Chapter14.Section06
