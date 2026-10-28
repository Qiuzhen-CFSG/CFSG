module
public import CFSG.Quasithin.Chapter14.Section06.SourceOrdinaryComponentMarking
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Small

/-!
# The odd prime guard for the actual source component

The simple star component rules out PSL_2(3). The original central-line
Bender exclusion rules out PSL_2(5), using its binary PSL_2(4) marking.
Every odd prime field in the original paired catalogue therefore has
parameter seven or greater than nine. The ordinary marked component
consumer supplies oddness from its Fermat--Mersenne parameter.

Source: Aschbacher--Smith 14.6.9, printed pp.1027--1028; E.2.2.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem fermat_mersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  intro he
  rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hpow : 1 < 2 ^ (2 ^ k) := one_lt_pow' (by decide) (by positivity)
    omega
  · by_cases hk0 : k = 0
    · simp only [hk0,pow_zero] at hk
      omega
    · have hev : Even (2 ^ k) := (show Even 2 by decide).pow_of_ne_zero hk0
      rw [←hk,he] at hev
      norm_num at hev

private theorem five_binary_model {D : Type*} [Group D]
    (hm : ClassicalGroup.IsPSL D 2 5) : ClassicalGroup.IsPSL D 2 (2^2) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eA := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  let e4 := (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour).some
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,⟨eA.trans e4.symm⟩⟩

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

/-- The actual source simple image excludes field three, and the original
central-line Bender exclusion removes field five. The resulting guard is
valid for every odd prime field, including the paired source catalogue. -/
theorem source_parabolic_odd_prime_guard
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup I) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) 2 p) :
    p = 7 ∨ 9 < p := by
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS).2.2
  have hs : ¬ Group.IsSolvable I := by
    intro hs
    let := hs
    apply hF
    rw [generalizedFitting_eq_fitting_of_solvable I,Fitting_eq_pcore I 2 hodd]
  have him := ChapterE.Structure.source_component_simple_image S hP hs K hK hgen
  have hn3 : p ≠ 3 := by
    intro he
    obtain ⟨F,hField,hfin,hcard,⟨eqv⟩⟩ := hm
    exact ChapterE.Witnesses.PairedOddLinearTwo.component_not_equiv_field_three
      (hcard.trans he) him.2.1 eqv
  have hn5 : p ≠ 5 := by
    intro he
    exact source_parabolic_bender_exclusion hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI S hS hP hmax hF K hK hgen
        (.linear 2 (by decide) (five_binary_model (he ▸ hm)))
  by_cases h9 : 9 < p
  · exact Or.inr h9
  · have htwo := hp.two_le
    interval_cases p <;> norm_num at *

/-- The ordinary marked component's Fermat--Mersenne row supplies both
literal odd-prime guards needed by the source rank contradiction. -/
theorem source_parabolic_ordinary_prime_guard
    (K : Subgroup I) (hK : IsComponent I K)
    (hgen : K ⊔ (S : Subgroup I) = ⊤)
    (eqv : (K ⧸ center K) ≃*
      K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP)))
    {p : ℕ} (hp : IsFermatOrMersennePrime p)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) :
    Odd p ∧ (p = 7 ∨ 9 < p) := by
  have ho := fermat_mersenne_odd hp
  exact ⟨ho,source_parabolic_odd_prime_guard hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI S hS hP hmax hF K hK.isCComponent hgen hp.1 ho
      (hm.of_mulEquiv eqv.symm)⟩

end Marked
end CFSG.Quasithin.Chapter14.Section06
