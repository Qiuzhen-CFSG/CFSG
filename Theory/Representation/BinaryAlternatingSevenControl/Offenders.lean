module

public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinaryOffender.Stability
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.SubgroupProductCard
/-!
# Native binary A₇ offender control

A faithful binary four-dimensional A₇ action has binary rank at most two.
Every involution moves exactly a plane, so no strong offender exists. A four
group centralizing a three-cycle fixes a plane and is a best offender. Sylow
self-normalization and the unique fixed line force all best offenders in a
Sylow subgroup to coincide. Its normalizer together with the pointwise fixer
of the Sylow-fixed line generates A₇. The proof uses actual subgroup maps and
works for arbitrary faithful four-dimensional actions.

Source: Aschbacher–Smith C.1.23(2), printed p.130, with B.4.2.7 and
B.5.1.2. The printed direct-product description of the plane fixer is not
used; the fixed-line generation statement is the native source interface.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped Pointwise
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem elementary_rank_le_two {A : Subgroup A7} (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  have hc := (primeRank_le_iff_elementary_card_le A7).mp
    (AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating.le) A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

theorem elementary_two_le_codim (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {A : Subgroup A7} (hA : IsElementaryTwo A) : 2 ≤ fixedCodim ρ A :=
  AlternatingSevenConjugatePair.le_fixedCodim_of_involutions ρ
    (fun t ht => (AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hf hd t ht).ge) hA

theorem no_strong_offender (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A,hA,hlt⟩
  have := elementary_rank_le_two hA
  have := elementary_two_le_codim ρ hf hd hA
  omega

theorem best_dimensions (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {A : Subgroup A7} (hA : IsBestOffender ρ A) :
    rank A = 2 ∧ Nat.card A = 4 ∧ Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 := by
  have hh := (isBestOffender_iff_of_not_strong ρ (no_strong_offender ρ hf hd) A).mp hA
  have hu := elementary_rank_le_two hA.1
  have hl := elementary_two_le_codim ρ hf hd hA.1
  have he : rank A = 2 := by omega
  refine ⟨he, ?_, ?_⟩
  · rw [hA.1.card_eq_two_pow_rank,he]
    rfl
  · have := fixedCodim_add_finrank ρ A
    omega

private theorem fixed_rank_two_of_central_cubic
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    {A : Subgroup A7} (hA : IsElementaryTwo A)
    (c : A7) (hc : c ∈ centralizer (A : Set A7))
    (hthree : (c : Equiv.Perm (Fin 7)).IsThreeCycle) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) = 2 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp A.subtype) (IsElementaryAbelian.isPGroup 2 A)
  have hcv : ρ c v ∈ fixedSpace ρ A := by
    intro a
    change ρ (a : A7) (ρ c v) = ρ c v
    rw [← Module.End.mul_apply, ← map_mul,hc a a.property,map_mul,Module.End.mul_apply]
    exact congrArg (ρ c) (hfix a)
  have hn : ρ c v ≠ 0 := by
    intro hz
    apply hv
    simpa only [ρ.inv_self_apply,map_zero] using congrArg (ρ c⁻¹) hz
  have hne : ρ c v ≠ v := fun he =>
    hv (binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd c hthree v he)
  let W := fixedSpace ρ A
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  have hcard : 2 < Nat.card W := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.two_lt_card_iff.mpr
    refine ⟨0,⟨v,hfix⟩,⟨ρ c v,hcv⟩,?_,?_,?_⟩
    · exact fun he => hv (congrArg Subtype.val he).symm
    · exact fun he => hn (congrArg Subtype.val he).symm
    · exact fun he => hne (congrArg Subtype.val he).symm
  have hl : 2 ≤ Module.finrank (ZMod 2) W := by
    by_contra h
    have hd1 : Module.finrank (ZMod 2) W ≤ 1 := by omega
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    norm_num at hh
    omega
  have hc := fixedCodim_add_finrank ρ A
  have hh := elementary_two_le_codim ρ hf hd hA
  change Module.finrank (ZMod 2) W = 2
  change fixedCodim ρ A + Module.finrank (ZMod 2) W = _ at hc
  omega

private theorem exists_best_centralized_by_threeCycle
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    ∃ A : Subgroup A7, IsBestOffender ρ A ∧
      ∃ c ∈ centralizer (A : Set A7), (c : Equiv.Perm (Fin 7)).IsThreeCycle := by
  classical
  let c : A7 := ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have hc : (c : Equiv.Perm (Fin 7)).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨b,d,hb2,hd2,hb1,hd1,hbd,hcb,hcd,hcomm⟩ :=
    alternatingGroup.threeCycle_exists_commuting_involutions c hc
  let A := zpowers b ⊔ zpowers d
  have hdc : zpowers d ≤ centralizer (zpowers b : Set A7) := by
    apply zpowers_le.mpr
    rintro _ ⟨n,rfl⟩
    exact (hcomm.zpow_left n).eq
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb2
  let : IsElementaryAbelian 2 (zpowers d) := IsElementaryAbelian.zpowers_of_pow_eq_one hd2
  have hel : IsElementaryAbelian 2 A := IsElementaryAbelian.sup_of_le_centralizer hdc
  have hbA : b ∈ A := (show zpowers b ≤ A from le_sup_left) (mem_zpowers b)
  have hdA : d ∈ A := (show zpowers d ≤ A from le_sup_right) (mem_zpowers d)
  have hA : IsElementaryTwo A := ⟨by
    intro he
    have : b ∈ (⊥ : Subgroup A7) := he ▸ hbA
    exact hb1 this,hel⟩
  let : Fintype A := Fintype.ofFinite A
  have hcard : 2 < Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.two_lt_card_iff.mpr
    exact ⟨1,⟨b,hbA⟩,⟨d,hdA⟩,
      fun he => hb1 (congrArg Subtype.val he).symm,
      fun he => hd1 (congrArg Subtype.val he).symm,
      fun he => hbd (congrArg Subtype.val he)⟩
  have hr : rank A = 2 := by
    have hle := elementary_rank_le_two hA
    by_contra hn
    have h1 : rank A ≤ 1 := by omega
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h1
    rw [← hA.card_eq_two_pow_rank] at hh
    norm_num only [pow_one] at hh
    omega
  have hAc : A ≤ centralizer ({c} : Set A7) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcb.eq.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcd.eq.symm))
  have hcA : c ∈ centralizer (A : Set A7) :=
    fun a ha => mem_centralizer_singleton_iff.mp (hAc ha)
  have hdim := fixed_rank_two_of_central_cubic ρ hf hd hA c hcA hc
  refine ⟨A,?_,c,hcA,hc⟩
  apply (isBestOffender_iff_of_not_strong ρ (no_strong_offender ρ hf hd) A).mpr
  refine ⟨hA,?_⟩
  have hh := fixedCodim_add_finrank ρ A
  omega

theorem exists_best_with_threeCycle_normalizer
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : ∃ A : Subgroup A7, A ≤ R ∧ IsBestOffender ρ A ∧
      ∃ c ∈ normalizer (A : Set A7), (c : Equiv.Perm (Fin 7)).IsThreeCycle := by
  obtain ⟨A,hA,c,hc,hthree⟩ := exists_best_centralized_by_threeCycle ρ hf hd
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 P R
  let f := (MulAut.conj g).toMonoidHom
  have hmap : (P : Subgroup A7).map f = (R : Subgroup A7) := congrArg Sylow.toSubgroup hg
  refine ⟨A.map f,?_,hA.map_conj ρ g,f c,?_,?_⟩
  · rw [← hmap]
    exact map_mono hAP
  · exact A.le_normalizer_map f (mem_map_of_mem f (centralizer_le_normalizer _ hc))
  · change (g.val*c.val*g.val⁻¹).cycleType = {3}
    rw [Equiv.Perm.cycleType_conj]
    exact hthree

private theorem four_intersect_and_generate
    {G : Type*} [Group G] [Finite G] (R A B : Subgroup G)
    (hR : Nat.card R = 8) (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (hAR : A ≤ R) (hBR : B ≤ R) (hne : A ≠ B) : A ⊓ B ≠ ⊥ ∧ A ⊔ B = R := by
  have hsup : A ⊔ B ≤ R := sup_le hAR hBR
  constructor
  · intro hbot
    let f : ((A : Set G) * (B : Set G)) → R := fun x => ⟨x,by
      obtain ⟨a,ha,b,hb,hab⟩ := x.property
      rw [← hab]
      exact R.mul_mem (hAR ha) (hBR hb)⟩
    have hi : Function.Injective f := fun x y h =>
      Subtype.ext (congrArg (fun z : R => (z : G)) h)
    have hle := Nat.card_le_card_of_injective f hi
    rw [hR] at hle
    have hc := card_set_mul_mul_card_inf A B
    rw [hbot,card_bot,mul_one,hA,hB] at hc
    omega
  · have hd : Nat.card (A ⊔ B : Subgroup G) ∣ 8 := hR ▸ card_dvd_of_le hsup
    have hl : Nat.card (A ⊔ B : Subgroup G) ≤ 8 := hR ▸ card_le_of_le hsup
    have hg : 4 < Nat.card (A ⊔ B : Subgroup G) := by
      by_contra hn
      have ha : A = A ⊔ B := eq_of_le_of_card_ge le_sup_left (by omega)
      have hba : B ≤ A := ha ▸ le_sup_right
      have hb : B = A := eq_of_le_of_card_ge hba (by omega)
      exact hne hb.symm
    have he : Nat.card (A ⊔ B : Subgroup G) = 8 :=
      (by decide : ∀ n ∈ Finset.range 9, n ∣ 8 → 4 < n → n = 8)
        _ (Finset.mem_range.mpr (by omega)) hd hg
    exact eq_of_le_of_card_ge hsup (by rw [hR,he])

private theorem sylow_card (R : Sylow 2 A7) : Nat.card R = 8 := by
  rw [R.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
  norm_num [Nat.factorial]
  rw [show (2520 : ℕ).factorization 2 = 3 by
    rw [show 2520 = 2^3*315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
  norm_num

theorem best_unique_in_sylow (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) {A B : Subgroup A7} (hAR : A ≤ R) (hBR : B ≤ R)
    (hA : IsBestOffender ρ A) (hB : IsBestOffender ρ B) : A = B := by
  by_contra hne
  obtain ⟨_,hAc,hAd⟩ := best_dimensions ρ hf hd hA
  obtain ⟨_,hBc,hBd⟩ := best_dimensions ρ hf hd hB
  obtain ⟨hI,hgen⟩ := four_intersect_and_generate R A B (sylow_card R) hAc hBc hAR hBR hne
  obtain ⟨t,ht,ht1⟩ := (A ⊓ B).bot_or_exists_ne_one.resolve_left hI
  let : IsElementaryAbelian 2 A := hA.1.2
  have ht2 : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t ht.1) ht1
  have htCodim := AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hf hd t ht2
  have htDim : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 2 := by
    have := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hAt : fixedSpace ρ A = fixedSpace ρ (zpowers t) :=
    Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ (zpowers_le.mpr ht.1))
      (hAd.trans htDim.symm)
  have hBt : fixedSpace ρ B = fixedSpace ρ (zpowers t) :=
    Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ (zpowers_le.mpr ht.2))
      (hBd.trans htDim.symm)
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ R := by
    intro v hv
    have hvB : v ∈ fixedSpace ρ B := by rw [hBt,← hAt]; exact hv
    let : MulAction A7 V := MulAction.compHom V ρ
    have hstab : A ⊔ B ≤ MulAction.stabilizer A7 v :=
      sup_le (fun a ha => hv ⟨a,ha⟩) (fun b hb => hvB ⟨b,hb⟩)
    intro r
    exact hstab (hgen.symm ▸ r.property)
  have hh := Submodule.finrank_mono hfix
  rw [hAd,sylow_fixed_finrank ρ hf hd R] at hh
  omega

theorem exists_unique_best_and_generation
    (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) : ∃ A : Subgroup A7, A ≤ R ∧ IsBestOffender ρ A ∧
      (∀ B : Subgroup A7, B ≤ R → IsBestOffender ρ B → B = A) ∧
      normalizer (A : Set A7) ⊔ subspaceKernel ρ (fixedSpace ρ R) ⊤ = ⊤ := by
  obtain ⟨A,hAR,hA,hc⟩ := exists_best_with_threeCycle_normalizer ρ hf hd R
  exact ⟨A,hAR,hA,(fun B hBR hB => best_unique_in_sylow ρ hf hd R hBR hAR hB hA),
    normalizer_sup_fixedKernel_of_threeCycle ρ hf hd R A hc⟩

/-- The actual A₇ embedding through A₈ ≃ SL₄(2) satisfies the native control theorem. -/
theorem natural_sylow_control (R : Sylow 2 A7) :
    ∃ A : Subgroup A7, A ≤ R ∧
      IsBestOffender AlternatingSevenConjugatePair.Model.natural A ∧
      (∀ B : Subgroup A7, B ≤ R →
        IsBestOffender AlternatingSevenConjugatePair.Model.natural B → B = A) ∧
      normalizer (A : Set A7) ⊔
        subspaceKernel AlternatingSevenConjugatePair.Model.natural
          (fixedSpace AlternatingSevenConjugatePair.Model.natural R) ⊤ = ⊤ :=
  exists_unique_best_and_generation AlternatingSevenConjugatePair.Model.natural
    AlternatingSevenConjugatePair.Model.natural_faithful
    AlternatingSevenConjugatePair.Model.four_dimension R

end Representation.BinaryAlternatingSevenControl
