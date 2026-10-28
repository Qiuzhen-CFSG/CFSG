module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.ModelComparison
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
/-!
# Eliminating the product row in the original component comparison

Each small B.5 model except binary SL₂ has order dividing 60480, whose
prime divisors are 2, 3, 5 and 7. The marked product row has a prime PSL₂
factor with defining prime at least 11. The actual central quotient
comparison forces that prime to divide the star component order, a
contradiction. In the remaining SL₂ case, the odd/binary model comparison
forces A₅ and contradicts the product-row congruence.

Thus the same selected K maps onto the whole generalized Fitting subgroup
of I/O₃′(I). This removes F.6.18(3) using actual isomorphisms and maps.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029. The further model
intersection and compatible block reconstruction remain separate steps.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC.C27Source
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open ChapterB.SourceInduction.ProjectiveLine
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]

omit [Finite E] in
private theorem small_model_linearTwo_or_card (h : SmallModels.Model E) :
    (∃ F : BinaryField, 2 ≤ F.degree ∧ F.degree ≤ 7 ∧ Nonempty (E ≃* SL(2,F.Carrier))) ∨
      Nat.card E ∣ 60480 := by
  cases h with
  | linearTwo F hlo hhi e => exact Or.inl ⟨F,hlo,hhi,⟨e⟩⟩
  | linearThree F hhi e =>
    right
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq]
    have hlo := F.degree_pos
    have hh : F.degree = 1 ∨ F.degree = 2 := by omega
    rcases hh with hh | hh <;> rw [hh] <;> norm_num
  | alternatingSix e =>
    right
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | alternatingSeven e =>
    right
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | tripleSix ec eq =>
    right
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center E),
      Nat.card_congr eq.toEquiv,Nat.card_congr ec.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | g2DerivedTwo e =>
    right
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    norm_num
  | linearFourTwo e =>
    right
    rw [Nat.card_congr e.toEquiv,Atlas.Order20160A8.sl4Two_card]
    norm_num

omit [Finite D] in
private theorem small_model_not_product (h : SmallModels.Model E)
    {S : Sylow 2 D} (r : FSource.ProductRow S)
    (e : (E ⧸ center E) ≃* r.first) : False := by
  have hp := r.field.prime_isPrime
  have hc : Nat.card r.field.Carrier = r.field.prime := by rw [r.field.card,r.degree,pow_one]
  have hodd : Odd r.field.prime := by rw [Nat.odd_iff]; have hh := r.congruence; omega
  have hoddF : Odd (Nat.card r.field.Carrier) := hc ▸ hodd
  have hlo : 11 ≤ r.field.prime := by have hh := r.congruence; omega
  let a := e.trans r.firstEquiv
  rcases small_model_linearTwo_or_card h with ⟨F,_,_,⟨b⟩⟩ | hd
  · have hz : center E = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hh := (centerCongr b ⟨x,hx⟩).property
      change b x ∈ center SL(2,F.Carrier) at hh
      rw [Theory.PSL2.sl2_center_eq_bot] at hh
      apply mem_bot.mpr
      apply b.injective
      exact (mem_bot.mp hh).trans b.map_one.symm
    let c : E ≃* (E ⧸ center E) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
    let F' : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField :=
      { Carrier := F.Carrier, degree := F.degree, degree_pos := F.degree_pos, card_eq := F.card_eq }
    obtain ⟨d⟩ := odd_linearTwo_binary_alternatingFive F'
      ⟨r.field.prime,1,hp,hodd,by decide,by simpa using hc⟩ b (c.trans a)
    exact primeRow_not_alternatingFive hp hc r.congruence ((c.trans a).symm.trans d)
  · have hpq : r.field.prime ∣ Nat.card (E ⧸ center E) := by
      rw [Nat.card_congr a.toEquiv]
      have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice hoddF
      rw [hc] at h
      have hd : r.field.prime ∣ Nat.card PSL(2,r.field.Carrier) * 2 :=
        h.symm ▸ dvd_mul_right r.field.prime (r.field.prime ^ 2 - 1)
      exact (hp.dvd_mul.mp hd).resolve_right (by intro hh; have := Nat.le_of_dvd (by decide) hh; omega)
    have hpN : r.field.prime ∣ 60480 := hpq.trans
      ((card_dvd_of_surjective (QuotientGroup.mk' (center E))
        (QuotientGroup.mk'_surjective _)).trans hd)
    have hpN' : r.field.prime ∣ 2^6 * 3^3 * 5 * 7 := by norm_num at hpN ⊢; exact hpN
    rcases hp.dvd_mul.mp hpN' with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp (hp.dvd_of_dvd_pow h)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow h)
          omega
      · have := Nat.le_of_dvd (by decide : 0 < 5) h
        omega
    · have := Nat.le_of_dvd (by decide : 0 < 7) h
      omega

omit [Finite D] in
private theorem small_model_not_product_component (h : SmallModels.Model E)
    (K : Subgroup D) (hK : IsComponent D K)
    {S : Sylow 2 D} (r : FSource.ProductRow S) (hr : K = r.first)
    (e : (E ⧸ center E) ≃* (K ⧸ center K)) : False := by
  have hc : 3 < Nat.card r.field.Carrier := by
    rw [r.field.card,r.degree,pow_one]
    have hh := r.congruence
    omega
  let : IsSimpleGroup PSL(2,r.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup K := ((MulEquiv.subgroupCongr hr).trans r.firstEquiv).isSimpleGroup
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hz : center K = ⊥ :=
    (inferInstance : (center K).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp ht))
  exact small_model_not_product h r (e.trans
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr hr)))



open scoped Pointwise
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




/-- The selected source component is exactly the generalized Fitting subgroup in the quotient. -/
theorem source_parabolic_f618_c27_fitting
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let A := (I1.subgroupOf I).map q
    let B := (I2.subgroupOf I).map q
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map I.subtype ≤ I ⊓ M ∧
      Input KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) (K.map I.subtype) ∧
      ChapterC.C27Source.SmallModels.Model
        (starImage (K.map I.subtype) (I1.pCoreIn 2) (K.map I.subtype)) ∧
      IsComponent (I ⧸ pPrimeCore 3 I) (K.map q) ∧
      (let C := K.map I.subtype
       let a := K.equivMapOfInjective I.subtype I.subtype_injective
       ∃ e : (starImage C (I1.pCoreIn 2) C ⧸ center (starImage C (I1.pCoreIn 2) C)) ≃*
           ((K.map q) ⧸ center (K.map q)),
         ∀ k : K, e (QuotientGroup.mk' (center (starImage C (I1.pCoreIn 2) C))
             (toStarImage C (I1.pCoreIn 2) (a k))) =
           QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k)) ∧
      ∃ S : Sylow 2 (I ⧸ pPrimeCore 3 I), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S) ∧
        (K.map q = generalizedFitting (I ⧸ pPrimeCore 3 I) ∧
          IsQuasisimple (generalizedFitting (I ⧸ pPrimeCore 3 I))) := by
  obtain ⟨K,hK,hn,hfit,hq,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩ :=
    source_parabolic_f618_c27_comparison hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  refine ⟨K,hK,hn,hfit,hq,ho,hi,hm,himage,hcomp,S,hS,hsource,?_⟩
  rcases hcase with ⟨r,hr,_⟩ | hf
  · obtain ⟨b,_⟩ := hcomp
    exact (small_model_not_product_component hm _ himage r hr b).elim
  · exact hf

end CFSG.Quasithin.Chapter14.Section06
