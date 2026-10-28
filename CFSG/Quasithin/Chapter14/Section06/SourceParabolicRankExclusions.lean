module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuotientElementary
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.NormalElementaryBound
public import Theory.GroupTheory.GeneralizedFitting.Solvable
public import CFSG.Quasithin.ChapterE.Section02.Structure.SmallNormalRank
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Component rank contradictions in original 14.6.9

The original span U_H has a normal elementary image of rank at least four
in the actual parabolic-core quotient. In the prime-field linear-two rows,
its actions on the normal component, or on the two exchanged components,
give that same image order at most four. Comparing its binary rank with
this cardinality excludes both component configurations at once. The
normal binary linear-three and derived symplectic rows instead give order
at most eight through their faithful component automorphism actions.

Source: Aschbacher--Smith 14.6.9, printed p.1028, using E.2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original rank-four hypothesis excludes the prime-field linear-two
star row for either a normal or an exchanged generating component. -/
theorem source_parabolic_odd_prime_exclusion
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
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup I) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hfield : Nat.card F = p) (hp : p = 7 ∨ 9 < p)
    (emodel : K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : False := by
  let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
  obtain ⟨hUE,hUS,hUN,_⟩ := source_span_sylow_normal hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS
  let : IsElementaryAbelian 2 U := hUE
  let W := U.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1 S hS).2.2
  have hs : ¬ Group.IsSolvable I := by
    intro hs
    let := hs
    apply hF
    rw [generalizedFitting_eq_fitting_of_solvable I,Fitting_eq_pcore I 2 hodd]
  have hupper : Nat.card W ≤ 4 :=
    ChapterE.Witnesses.PairedOddLinearTwo.source_star_elementary_card_le_four
      ChapterA.Section02.theoremA_knownSimple (Chapter3.sqtk_of_mem_H hG hI.1.1)
      S hP hs K hK hgen ho hfield hp emodel U hUS hUN
  have hlower : 4 ≤ primeRank 2 W :=
    (source_parabolic_quotient_elementary_rank_four hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI S hS hF hrank hP).2.2.2
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2) W] at hlower
  have hlog := Nat.log_mono_right (b := 2) hupper
  norm_num at hlog
  omega

/-- The two surviving small binary rows cannot occur as the normal
generating component under the original rank-four hypothesis. -/
theorem source_parabolic_small_binary_exclusion
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
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup I) = ⊤)
    (hm : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) 3 2 ∨
      Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) ≃*
        commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
  obtain ⟨hUE,_,_,_⟩ := source_span_sylow_normal hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS
  let : IsElementaryAbelian 2 U := hUE
  let W := U.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI.1 S hS).2.2
  have hs : ¬ Group.IsSolvable I := by
    intro hs
    let := hs
    apply hF
    rw [generalizedFitting_eq_fitting_of_solvable I,Fitting_eq_pcore I 2 hodd]
  have hupper : Nat.card W ≤ 8 :=
    ChapterE.Structure.source_star_small_binary_elementary_card_le_eight
      S hP hs K hK hgen hm U
  have hlower : 4 ≤ primeRank 2 W :=
    (source_parabolic_quotient_elementary_rank_four hG T hempty hM hunique hmany
      hcard e hab H hH u hu I hI S hS hF hrank hP).2.2.2
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2) W] at hlower
  have hlog := Nat.log_mono_right (b := 2) hupper
  norm_num at hlog
  omega

end CFSG.Quasithin.Chapter14.Section06
