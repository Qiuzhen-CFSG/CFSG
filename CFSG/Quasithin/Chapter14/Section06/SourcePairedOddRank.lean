module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCentralizerNormalizer
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Alternating
public import CFSG.KnownSimple.PrimeToFifteen
public import Theory.GroupTheory.CommutingThreePrimeRank
/-!
# The paired normalizer's odd-rank contradiction

In the paired branch of original 14.6.9, the two alternating blocks each
contribute a cyclic subgroup at both odd primes 3 and 5. Every ordinary
component of a K-group has order divisible by at least one of these primes:
otherwise the known-simple prime-to-fifteen theorem makes it solvable.
Thus a component centralizing both blocks forces odd-prime rank at least
three, contrary to the SQTK condition.

The final theorem uses the literal normalizer of the source centralizer D.
Its remaining input is precisely the component-centralization statement
obtained from 1.2.8; all normalizer, block, and SQTK data come from the original
source hypotheses.

Source: Aschbacher–Smith, original 14.6.9, printed p. 1026.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_five_center_coprime {L : Type*} [Group L] [Finite L]
    (hL : IsAlternatingBlock L 5) {p : ℕ} (ho : Odd p) :
    Nat.Coprime p (Nat.card (center L)) := by
  obtain ⟨e⟩ := hL.2.2.quotient_iso
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hZ : center L ≤ pCore 2 L := by
    intro z hz
    have hfz : f z ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨b,rfl⟩ := hf a
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hz b)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hfz
    exact (QuotientGroup.eq_one_iff z).mp (e.map_eq_one_iff.mp hfz)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).to_le hZ |>.exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

private theorem alternating_five_dvd_card {L : Type*} [Group L] [Finite L]
    (hL : IsAlternatingBlock L 5) {p : ℕ} (hp : p = 3 ∨ p = 5) : p ∣ Nat.card L := by
  obtain ⟨e⟩ := hL.2.2.quotient_iso
  have hc : Nat.card (L ⧸ pCore 2 L) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd : p ∣ Nat.card (L ⧸ pCore 2 L) := by
    rcases hp with rfl | rfl <;> rw [hc] <;> decide
  exact hd.trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _))

/-- An ordinary component in an SQTK group cannot centralize two commuting A₅ blocks. -/
theorem paired_alternating_component_exclusion
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (P Q A : Subgroup G) (hP : IsAlternatingBlock P 5) (hQ : IsAlternatingBlock Q 5)
    (hA : IsComponent G A) (hPQ : P ≤ centralizer (Q : Set G))
    (hAP : A ≤ centralizer (P : Set G)) (hAQ : A ≤ centralizer (Q : Set G)) : False := by
  let := hA.2
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  have hd : 3 ∣ Nat.card A ∨ 5 ∣ Nat.card A := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable A
      (KnownSimple.isSolvable_of_coprime_three_five A (hG.isKGroup.subgroup A)
        (Nat.prime_three.coprime_iff_not_dvd.mpr hn.1)
        (Nat.prime_five.coprime_iff_not_dvd.mpr hn.2))
  have hbad (p : ℕ) (hp : p = 3 ∨ p = 5) (hdA : p ∣ Nat.card A) : False := by
    have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
    have ho : Odd p := by rcases hp with rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hprime⟩
    have hlo := primeRank_three_of_commuting_of_centers_coprime P Q A hPQ hAP hAQ
      (alternating_five_center_coprime hP ho) (alternating_five_center_coprime hQ ho)
      (alternating_five_dvd_card hP hp) (alternating_five_dvd_card hQ hp) hdA
    have hhi := hG.stronglyQuasithin p hprime ho
    omega
  rcases hd with hd | hd
  · exact hbad 3 (Or.inl rfl) hd
  · exact hbad 5 (Or.inr rfl) hd
end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC ChapterC.Section05.BlockAnalysis
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


/-- The literal paired normalizer is of characteristic two once its ordinary
components centralize the actual two-residual of I. -/
theorem source_paired_centralizer_characteristicTwo_of_component_centralization
    (I Λ : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hne : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≠ ⊥)
    (hcentral : let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
      ∀ A : Subgroup ID, IsComponent ID A →
        (pResidual 2 I).map I.subtype ≤ centralizer (A.map ID.subtype : Set G)) :
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
    generalizedFitting ID = pCore 2 ID := by
  let K := (pResidual 2 I).map I.subtype
  let D := ((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G)
  let ID := normalizer (D : Set G)
  obtain ⟨hIID,_,_,hID,_,_⟩ := source_paired_centralizer_normalizer_data hG T hempty hM
    hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I Λ hI c hne
  change generalizedFitting ID = pCore 2 ID
  by_contra hF
  obtain ⟨S,z,A,_,_,_,hA,_⟩ := source_paired_centralizer_ordinary_component hG T hempty hM
    hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I Λ hI c hne hF
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  let P := (b.block i).map I.subtype
  let Q := (b.block j).map I.subtype
  have hPI : P ≤ I := map_subtype_le _
  have hQI : Q ≤ I := map_subtype_le _
  have hPID : P ≤ ID := hPI.trans hIID
  have hQID : Q ≤ ID := hQI.trans hIID
  have hPK : P ≤ K := map_mono ((le_iSup b.block i).trans_eq b.generate)
  have hQK : Q ≤ K := map_mono ((le_iSup b.block j).trans_eq b.generate)
  have hP : IsAlternatingBlock (P.subgroupOf ID) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hPID).symm h.block
  have hQ : IsAlternatingBlock (Q.subgroupOf ID) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hQID).symm h'.block
  have hcomm := hcentral A hA
  apply paired_alternating_component_exclusion hID (P.subgroupOf ID) (Q.subgroupOf ID) A hP hQ hA
  · intro p hp q hq
    exact Subtype.ext (h'.commute hp q hq)
  · intro a ha p hp
    exact Subtype.ext ((hcomm (hPK hp) a (mem_map_of_mem ID.subtype ha)).symm)
  · intro a ha q hq
    exact Subtype.ext ((hcomm (hQK hq) a (mem_map_of_mem ID.subtype ha)).symm)
end CFSG.Quasithin.Chapter14.Section06
