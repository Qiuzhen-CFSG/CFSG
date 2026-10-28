module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponentModels
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Classification
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor

/-!
# The marked ordinary component in the nonsolvable source branch

The vanishing odd core and F*(I) != O_2(I) produce an ordinary component.
The original 14.6.7 component-join theorem and IMin minimality make this
same component generate I with the prescribed Sylow intersection. The
complete 1.1.5 classifier therefore marks it using the original involution.
In the minimal-parabolic branch its actual star image is identified with
its central quotient. The E.2.2 family list and the marked odd-parameter
restrictions are then applied to that same quotient. The degree-three
field-three and PSL_2(9) overlaps remain explicit; no C-component is
assumed to be an ordinary component.

Source: Aschbacher--Smith 14.6.7 and 14.6.9, printed pp.1024,1027--1028;
1.1.5(3), printed pp.501--503; E.2.2, printed pp.215--216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

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


omit hindex hmove hproduct hU3 hlocal in
/-- Ordinary components of the original minimal outside choice generate with
its literal Sylow intersection and carry the marked source action. -/
theorem source_iMin_ordinary_component_marking
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I) :
    ∃ z : G, z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z ∧
      ∀ K : Subgroup I, IsComponent I K →
        K ⊔ (S : Subgroup I) = ⊤ ∧
        K.map I.subtype = ⁅K.map I.subtype, zpowers z⁆ ∧
        ¬ K.map I.subtype ≤ Mc ∧ HasModelAction115 K z := by
  obtain ⟨⟨z,hz,h115⟩,_,_,hcomp⟩ := source_lemma_14_6_7 hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1 S hS
  refine ⟨z,hz,h115,?_⟩
  intro K hK
  have hJI : K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) ≤ I :=
    sup_le (map_subtype_le _) inf_le_right
  have he : K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) = I :=
    le_antisymm hJI (hI.2 (hcomp K hK).2 hJI)
  have hgen : K ⊔ (S : Subgroup I) = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,hS,he,←MonoidHom.range_eq_map,range_subtype]
  exact ⟨hgen,Chapter1.lemma_1_1_5_three_of_local_classification hG
    (fun _ _ _ => ChapterA.Section02.theoremsABC_knownSimple)
    (fun _ _ _ _ _ _ d hm => d.classify hm) I S Mc z h115 K hK⟩

/-- The non-characteristic-two original choice constructs an ordinary
component with the actual marked action and Sylow-generation equality. -/
theorem source_noncharacteristic_ordinary_component
    (I : Subgroup G) (hF : generalizedFitting I ≠ pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    ∃ (S : Sylow 2 I) (z : G) (K : Subgroup I),
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z ∧
      IsComponent I K ∧ K.IsCComponent ∧ K ⊔ (S : Subgroup I) = ⊤ ∧
      K.map I.subtype = ⁅K.map I.subtype, zpowers z⁆ ∧
      ¬ K.map I.subtype ≤ Mc ∧ HasModelAction115 K z := by
  obtain ⟨⟨S,hS⟩,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1.1
  have ho := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1.1 S hS).2.2
  obtain ⟨K,hK⟩ := exists_component_of_oddCore_eq_bot ho hF
  obtain ⟨z,hz,h115,hcomp⟩ := source_iMin_ordinary_component_marking hG T hempty hM hunique
    hmany hcard e hab H hH u hu I hI S hS
  exact ⟨S,z,K,hS,hz,h115,hK,hK.isCComponent,hcomp K hK⟩


omit hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal in
/-- The actual 1.1.5 marking restricts the odd rows on the central quotient
of an ordinary component. The square field nine and degree-three field
three overlaps are retained explicitly. -/
theorem source_ordinary_marked_odd_parameters
    {I : Subgroup G} {S : Sylow 2 I} {z : G}
    (h115 : Chapter1.Lemma115Hypotheses I S Mc z)
    (K : Subgroup I) (hK : IsComponent I K)
    (hm : ChapterA.Section02.IsTheoremCOddModel (K ⧸ center K)) :
    ClassicalGroup.IsPSL (K ⧸ center K) 3 3 ∨
    ClassicalGroup.IsPSU (K ⧸ center K) 3 3 ∨
    ClassicalGroup.IsPSL (K ⧸ center K) 2 9 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL (K ⧸ center K) 2 p := by
  let : IsQuasisimple K := hK.2
  obtain ⟨_,α,P,_,d,_⟩ := h115.component_inputs K hK
  cases hm with
  | linear_two p n hp ho hn hm =>
    rcases Chapter1.QuasisimpleInvolutions.linear_two_exponent ho hn hm with ⟨hn,_⟩ | hn
    · subst n
      simp only [pow_one] at hm
      exact Or.inr (Or.inr (Or.inr ⟨p,d.linear_two_prime_parameter hp ho hm,hm⟩))
    · subst n
      by_cases hp3 : p = 3
      · exact Or.inr (Or.inr (Or.inl (by simpa only [hp3,show 3 ^ 2 = 9 from rfl] using hm)))
      · have hp2 := hp.two_le
        have hpodd := Nat.odd_iff.mp ho
        exact (d.linear_two_square_excluded hp ho (by omega) hm).elim
  | linear_three p hp ho hm =>
    exact Or.inl (d.linear_three_parameters p hp ho hm ▸ hm)
  | unitary_three p hp ho hm =>
    exact Or.inr (Or.inl (d.unitary_three_parameter p hp ho hm ▸ hm))

/-- Both classifications now concern the same ordinary component and the
same involution from 14.6.7. Its literal star image is its central quotient. -/
theorem source_ordinary_component_lists_or_factorization
    (I : Subgroup G) (hF : generalizedFitting I ≠ pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (∃ (S : Sylow 2 I) (z : G),
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      z ∈ centralInvolutions T ∧ Chapter1.Lemma115Hypotheses I S Mc z ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
        ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I ∧
      ∃ K : Subgroup I, IsComponent I K ∧ K ⊔ (S : Subgroup I) = ⊤ ∧
        K.map I.subtype = ⁅K.map I.subtype, zpowers z⁆ ∧
        ¬ K.map I.subtype ≤ Mc ∧ HasModelAction115 K z ∧
        Nonempty ((K ⧸ center K) ≃*
          K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) ∧
        ((ClassicalGroup.IsPSL (K ⧸ center K) 3 3 ∨
          ClassicalGroup.IsPSU (K ⧸ center K) 3 3 ∨
          ClassicalGroup.IsPSL (K ⧸ center K) 2 9 ∨
          ∃ p : ℕ, IsFermatOrMersennePrime p ∧
            ClassicalGroup.IsPSL (K ⧸ center K) 2 p) ∨
          ClassicalGroup.IsPSL (K ⧸ center K) 3 2 ∨
          Nonempty ((K ⧸ center K) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))) ∨
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_minimal_parabolic_or_factorization hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI with ⟨S,hS,hP,hmax⟩ | hf
  · have ho := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI.1.1 S hS).2.2
    obtain ⟨K,hK⟩ := exists_component_of_oddCore_eq_bot ho hF
    let : IsQuasisimple K := hK.2
    obtain ⟨z,hz,h115,hmarks⟩ := source_iMin_ordinary_component_marking hG T hempty hM
      hunique hmany hcard e hab H hH u hu I hI S hS
    obtain ⟨hgen,hcomm,hout,hmodel⟩ := hmarks K hK
    have hs : ¬ Group.IsSolvable I := by
      intro hs
      let := hs
      let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
      let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
      exact Group.IsPerfect.not_isSolvable K inferInstance
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)
    obtain ⟨hsimple,hcomp,_,_⟩ := ChapterE.Structure.source_component_simple_image
      S hP hs K hK.isCComponent hgen
    let : IsSimpleGroup (K.map q) := hsimple
    let : IsQuasisimple (K.map q) := hcomp.2
    let f : Covering K (K.map q) :=
      { toMonoidHom := q.subgroupMap K, surjective := q.subgroupMap_surjective K }
    let eqv : (K ⧸ center K) ≃* K.map q :=
      (QuotientGroup.quotientMulEquivOfEq f.ker_eq_center_of_isSimple.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
    refine Or.inl ⟨S,z,hS,hz,h115,hP,hmax,K,hK,hgen,hcomm,hout,hmodel,⟨eqv⟩,?_⟩
    rcases source_parabolic_component_models hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI.1.1 S hS hP hmax hF K hK.isCComponent hgen with hm | hm | hm
    · exact Or.inl (source_ordinary_marked_odd_parameters h115 K hK (hm.of_mulEquiv eqv))
    · exact Or.inr (Or.inl (hm.of_mulEquiv eqv))
    · obtain ⟨eD⟩ := hm
      exact Or.inr (Or.inr ⟨eqv.trans eD⟩)
  · exact Or.inr hf

end CFSG.Quasithin.Chapter14.Section06
