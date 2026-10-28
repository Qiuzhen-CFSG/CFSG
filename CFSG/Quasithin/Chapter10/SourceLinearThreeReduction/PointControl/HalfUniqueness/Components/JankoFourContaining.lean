module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SporadicSmallContaining
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Recognition
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# The final J4 containing quotient in source 10.2.6

The original orbit quotient is the product of two copies of L/O₂(L).
Under containment in K, both copies survive after removing the two-core,
so their squared order divides |K/O₂(K)|. The certified J4 order excludes
this for every actual model in the nonnormal-component catalogue. Only
2, 3 and 11 can have squares dividing that order; the odd PSL₂ branch
then reduces to PSL₂(11), whose factor five rules it out.

The same order excludes every nonabelian Suzuki quotient, giving a cubic
in the original factor. Distinctness and the existing ranked-enlargement
contradiction now exclude either original J4 containing component.
The exchanger, relative normality and literal half-join remain unchanged.
No J4 two-local classification or recognition callback is assumed.

The complete containing-pair consumer is in Components.Completion. The
zero-kernel binary-three normalizer and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt comes from
qt-d-10-nona5-point-selection and is finally discharged by
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12(17) and 10.2.6, pp.47--48,748--749;
GLS3 Table 5.3i. The J4 order proof uses the native ATLAS matrix carrier.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1

private theorem square_prime {p : ℕ} (hp : p.Prime) (hd : p ^ 2 ∣ 86775571046077562880) :
    p = 2 ∨ p = 3 ∨ p = 11 := by
  have hpd : p ∣ 86775571046077562880 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  have he : 86775571046077562880 = 2^21*3^3*5*7*11^3*23*29*31*37*43 := by norm_num
  rw [he] at hpd
  simp only [hp.dvd_mul, or_assoc] at hpd
  rcases hpd with h | h | h | h | h | h | h | h | h | h
  · have he : p = 2 := (Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 2) h)
    exact Or.inl he
  · have he : p = 3 := (Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 3) h)
    exact Or.inr (Or.inl he)
  · have he : p = 5 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h)
    exact False.elim ((by decide : ¬ 5^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 7 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h)
    exact False.elim ((by decide : ¬ 7^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 11 := (Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 11) h)
    exact Or.inr (Or.inr he)
  · have he : p = 23 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23)).mp h)
    exact False.elim ((by decide : ¬ 23^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 29 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29)).mp h)
    exact False.elim ((by decide : ¬ 29^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 31 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp h)
    exact False.elim ((by decide : ¬ 31^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 37 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37)).mp h)
    exact False.elim ((by decide : ¬ 37^2 ∣ 86775571046077562880) (he ▸ hd))
  · have he : p = 43 := ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43)).mp h)
    exact False.elim ((by decide : ¬ 43^2 ∣ 86775571046077562880) (he ▸ hd))

/-- The original Suzuki simple quotient does not divide the J4 order. -/
theorem suzuki_order_not_dvd_jankoFour {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card Janko4.Model := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega),Janko4.Cardinality.model_card]
  intro hd
  have hb : m ≤ 4 := by
    by_contra h
    have hp : (2 ^ (2*m+1)) ^ 2 ∣ 86775571046077562880 :=
      (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hd
    have hd22 : 2^22 ∣ 86775571046077562880 := by
      apply dvd_trans _ hp
      rw [←pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    norm_num at hd22
  interval_cases m <;> norm_num at hd

/-- No nonsolvable model from the original nonnormal catalogue has order
whose square divides the J4 order. -/
theorem nonnormal_model_square_not_dvd_jankoFour
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hm : Section02.NonnormalCComponentModel Q) :
    ¬ (Nat.card Q)^2 ∣ Nat.card Janko4.Model := by
  rw [Janko4.Cardinality.model_card]
  intro hd
  cases hm with
  | suzuki m hm he =>
    apply suzuki_order_not_dvd_jankoFour hm
    rw [←Nat.card_congr he.some.toEquiv,Janko4.Cardinality.model_card]
    exact (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hd
  | janko he =>
    rw [Nat.card_congr he.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | linear_even n hn he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hc : Nat.card Q = 2^n * ((2^n)^2-1) := by
      rw [Nat.card_congr e.toEquiv,←Nat.card_congr
        (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F).toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
    rw [hc] at hd
    have hb : n ≤ 10 := by
      by_contra h
      have hp : (2^n)^2 ∣ 86775571046077562880 :=
        (pow_dvd_pow_of_dvd (dvd_mul_right _ _) 2).trans hd
      have hd22 : 2^22 ∣ 86775571046077562880 := by
        apply dvd_trans _ hp
        rw [←pow_mul]
        exact Nat.pow_dvd_pow 2 (by omega)
      norm_num at hd22
    interval_cases n <;> norm_num at hd
  | linear_prime p hp ho he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    have hgt : 3 < p := by
      rw [←hF]
      apply Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF.symm ▸ ho)
      intro hsol
      let := hsol
      let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
      let : Nontrivial Q := Function.Surjective.nontrivial
        (QuotientGroup.mk'_surjective (center Q))
      exact Group.IsPerfect.not_isSolvable Q
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    have hc : Nat.card Q * 2 = p * (p^2-1) := by
      rw [Nat.card_congr e.toEquiv]
      simpa only [hF] using Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
        (F := F) (hF.symm ▸ ho)
    have hcop : p.Coprime 2 := (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      omega)
    have hpQ : p ∣ Nat.card Q := hcop.dvd_of_dvd_mul_right
      (hc.symm ▸ dvd_mul_right p (p^2-1))
    have hs := square_prime hp ((pow_dvd_pow_of_dvd hpQ 2).trans hd)
    have heq : p = 11 := by omega
    rw [heq] at hc
    have hcard : Nat.card Q = 660 := by omega
    rw [hcard] at hd
    norm_num at hd

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The two original quotient factors both survive the containing two-core quotient. -/
theorem source_quotient_square_dvd_of_orbit_le
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {K : Subgroup G} (hOK : localOrbit T L ≤ K) :
    (Nat.card (L ⧸ pCore 2 L)) ^ 2 ∣ Nat.card (K ⧸ pCore 2 K) := by
  let O := localOrbit T L
  let A := O.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := q.subgroupMap A
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective A.subtype A.subtype_injective
  let a : O ≃* A := (subgroupOfEquivOfLe hOK).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (f.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective A) hk)
  obtain ⟨e⟩ := source_nonnormal_orbit_product_equiv D hn
  have hc : Nat.card ((A.map q) ⧸ pCore 2 (A.map q)) =
      (Nat.card (L ⧸ pCore 2 L)) ^ 2 := by
    rw [←Nat.card_congr b.toEquiv,Nat.card_congr e.toEquiv,Nat.card_prod,pow_two]
  rw [←hc]
  exact (card_quotient_dvd_card _).trans (card_subgroup_dvd_card _)


variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- A J4 containing component cannot contain the entire original orbit. -/
theorem not_orbit_le_of_jankoFour_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {K : Subgroup G} (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ¬ localOrbit T L ≤ K := by
  intro hOK
  let := D.quasisimple
  apply nonnormal_model_square_not_dvd_jankoFour
    (Selection.ModuleChoice.component_quotient_model D hn)
  rw [←Nat.card_congr hm.some.toEquiv]
  exact source_quotient_square_dvd_of_orbit_le D hn hOK

/-- Distinctness for the first literal J4 quotient requires no local catalogue. -/
theorem ContainingPair.distinct_of_first_jankoFour_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Janko4.Model)) : K₁ ≠ K₂ := by
  intro he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans hm.some
  apply not_orbit_le_of_jankoFour_quotient D hn ⟨b⟩
  rw [C.orbit_eq]
  apply sup_le
  · simpa only [map_subgroupOf_eq_of_le C.left_le] using map_mono (f := H.subtype) C.first_le
  · have hh := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le,←he] at hh

/-- The second-factor distinctness keeps the original exchanger. -/
theorem ContainingPair.distinct_of_second_jankoFour_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Janko4.Model)) : K₁ ≠ K₂ := by
  intro he
  subst K₂
  exact C.distinct_of_first_jankoFour_quotient hn hm rfl

/-- Exclude the first actual J4 containing quotient. -/
theorem ContainingPair.impossible_of_first_jankoFour_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Janko4.Model)) : False := by
  apply C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_jankoFour_quotient hn hm)
  apply C.three_dvd_of_first_quotient_without_suzuki hn
  intro m hmm
  rw [Nat.card_congr hm.some.toEquiv]
  exact suzuki_order_not_dvd_jankoFour hmm

/-- Exclude the second actual J4 containing quotient. -/
theorem ContainingPair.impossible_of_second_jankoFour_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Janko4.Model)) : False := by
  apply C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_jankoFour_quotient hn hm)
  apply C.three_dvd_of_second_quotient_without_suzuki hn
  intro m hmm
  rw [Nat.card_congr hm.some.toEquiv]
  exact suzuki_order_not_dvd_jankoFour hmm

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
