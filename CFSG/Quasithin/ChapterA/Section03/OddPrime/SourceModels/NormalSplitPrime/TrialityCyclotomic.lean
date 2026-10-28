module
public import Theory.FieldTheory.OddQuadraticCoefficientLift
public import Theory.SpecificGroups.Triality.OddDegreeFieldActors
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TrialitySubfield
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix

/-!
# Fixed cyclotomic planes for triality field actors

For p > 3, the actual coefficient order gives n = p*m. Fermat's congruence
transfers the third or sixth cyclotomic divisor from 2^n to 2^m. The proved
cyclotomic tori give an elementary p-square in the smaller genuine triality
carrier; the binary endpoint uses the checked seven-plane. TrialitySubfield
embeds this plane in the fixed subgroup of the SAME coefficient actor.
Its faithful inner image and the disjoint outside order-p actor force rank
three in the specified full-inner automorphism overgroup.

This discharges the remaining triality field rows in Aschbacher–Smith A.3.18,
pp.51–53. ExceptionalCyclotomic applies it to the literal ambient extension.
The imported torus constructions retain the original graph-field and central
quotient conventions of GLS3 §§2.2–2.6 and §6.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.Standard.ConcreteBruhat.FixedDescent
open Theory.AlgebraicGroup.StandardRootSystem
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
namespace TrialityCyclotomic

private theorem elementary_of_plane {G : Type*} [Group G]
    {p d : ℕ} [Fact p.Prime] [NeZero d] (hd : p ∣ d)
    (f : Multiplicative (ZMod d × ZMod d) →* G) (hf : Function.Injective f) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card (Multiplicative (ZMod d)) by simpa using hd)
  let C := zpowers a
  let : IsElementaryAbelian p C := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (C × C) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p C) x.2) }
  let j : C × C →* Multiplicative (ZMod d × ZMod d) := {
    toFun := fun x => Multiplicative.ofAdd (x.1.val.toAdd, x.2.val.toAdd)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : Multiplicative (ZMod d × ZMod d) => Multiplicative.ofAdd z.toAdd.1) h)
    · exact Subtype.ext (congrArg (fun z : Multiplicative (ZMod d × ZMod d) => Multiplicative.ofAdd z.toAdd.2) h)
  let k := f.comp j
  have hk := hf.comp hj
  let : IsElementaryAbelian p k.range :=
    IsElementaryAbelian.of_surjective k.rangeRestrict k.rangeRestrict_surjective
  refine ⟨k.range, inferInstance, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hk).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

open Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori

private theorem exists_elementary_three (m : ℕ) (hm : 0 < m) (hl : 1 < m)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2^m)^2 + 2^m + 1) :
    ∃ E : Subgroup (BinaryCarrier m hm), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨d⟩ := PhiThree.exists_twistedPlane m hm hl p hp hd
  obtain ⟨x, hx⟩ := PhiThree.exists_langWitness m hm hl
  let f := (((MulAut.conj x).toMonoidHom).comp d.embedding).codRestrict
    (fixedSubgroup (binaryParameters m hm))
    (fun z => PhiThree.conjugate_mem_fixed x hx _ (d.twisted_fixed z))
  let e := carrierFixedEquiv (binaryParameters m hm) rfl
  have hf : Function.Injective (e.symm.toMonoidHom.comp f) := by
    apply e.symm.injective.comp
    intro a b h
    exact d.injective ((MulAut.conj x).injective (congrArg Subtype.val h))
  have hc : p ∣ Nat.card (BinaryCarrier m hm) := by
    rw [card_carrier_factorization]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (dvd_pow hd (by decide : 2 ≠ 0)) _) _) _
  have hd' : p ∣ PhiThree.primaryOrder m p := by
    apply (Fact.out : p.Prime).dvd_of_dvd_pow
    rw [PhiThree.primaryOrder_sq m hm hp hd]
    exact Nat.dvd_ordProj_of_dvd Nat.card_pos.ne' Fact.out hc
  exact elementary_of_plane hd' (e.symm.toMonoidHom.comp f) hf

private theorem exists_elementary_six (m : ℕ) (hm : 0 < m) (hl : 1 < m)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2^m)^2 - 2^m + 1) :
    ∃ E : Subgroup (BinaryCarrier m hm), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨d⟩ := PhiSix.twistedPlane_nonempty m hm hl p hp hd
  obtain ⟨x⟩ := PhiSix.langWitness_nonempty m hm hl
  let : NeZero (p ^ (PhiSix.modulus (2^m)).factorization p) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact elementary_of_plane (Nat.dvd_ordProj_of_dvd (by positivity) Fact.out hd)
    (d.carrierEmbedding x) (d.carrierEmbedding_injective x)

private theorem cyclotomic_descends {n m p : ℕ} [Fact p.Prime] (hnm : n = p*m) :
    ((p ∣ (2^n)^2 + 2^n + 1) ↔ (p ∣ (2^m)^2 + 2^m + 1)) ∧
    ((p ∣ (2^n)^2 - 2^n + 1) ↔ (p ∣ (2^m)^2 - 2^m + 1)) := by
  have he : (2^n : ZMod p) = 2^m := by
    rw [hnm, Nat.mul_comm p m, pow_mul, ZMod.pow_card]
  have hnq : 2^n ≤ (2^n)^2 := Nat.le_self_pow (by decide) _
  have hmq : 2^m ≤ (2^m)^2 := Nat.le_self_pow (by decide) _
  constructor
  · rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [he]
  · rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hnq, Nat.cast_sub hmq]
    rw [he]

/-- Each remaining cyclotomic prime has an elementary square fixed by the
same coefficient actor; the smaller group is embedded with the actual marking. -/
theorem exists_fixed_elementary (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hd : p ∣ (2^n)^2 + 2^n + 1 ∨ p ∣ (2^n)^2 - 2^n + 1)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p) :
    ∃ E : Subgroup (BinaryCarrier n hn), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (coefficientAction _ σ).fixedSubgroup := by
  have hp3 : ¬ 3 ∣ p := fun h => by
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp h
    omega
  have hc : Nat.card (CoefficientAut (binaryParameters n hn)) = 3*n :=
    GaloisField.card_ringAut 2 (3*n) (by omega)
  have hn' : p ∣ n := by
    have hh := orderOf_dvd_natCard σ
    rw [hσ, hc] at hh
    exact (Fact.out : p.Prime).dvd_mul.mp hh |>.resolve_left (fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)
  obtain ⟨m, hnm⟩ := hn'
  have hm : 0 < m := by nlinarith
  obtain ⟨k, hk, hfix⟩ := exists_fixed_carrier_embedding n hn m hm hp3 hnm σ hσ
  have hd' : p ∣ (2^m)^2 + 2^m + 1 ∨ p ∣ (2^m)^2 - 2^m + 1 :=
    hd.elim (fun h => Or.inl ((cyclotomic_descends hnm).1.mp h))
      (fun h => Or.inr ((cyclotomic_descends hnm).2.mp h))
  have hsmall : ∃ E : Subgroup (BinaryCarrier m hm),
      IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
    by_cases hl : 1 < m
    · exact hd'.elim (exists_elementary_three m hm hl hp) (exists_elementary_six m hm hl hp)
    · have hm1 : m = 1 := by omega
      subst m
      have hp7 : p = 7 := by
        rcases hd' with h | h
        · norm_num at h
          exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp h).resolve_left (Fact.out : p.Prime).ne_one
        · norm_num at h
          have hh := Nat.le_of_dvd (by decide : 0 < 3) h
          omega
      rw [hp7]
      obtain ⟨E, hE, hcard, _⟩ := OddDegreeFieldActors.exists_fixed_seven_plane 1
        (by decide) (by decide) 1 (by simp)
      exact ⟨E, hE, hcard⟩
  obtain ⟨E, hE, hcard⟩ := hsmall
  let := hE
  let B := E.map k
  let : IsElementaryAbelian p B := IsElementaryAbelian.map k
  refine ⟨B, inferInstance, ?_, ?_⟩
  · rw [card_map_of_injective hk, hcard]
  · rintro _ ⟨x, _, rfl⟩
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hfix x)
/-- The fixed cyclotomic subsystem and a noninner coefficient actor give an elementary
subgroup of rank three in the literal automorphism overgroup. -/
theorem field_actor_rank_three (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hpgt : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (A : Subgroup (MulAut (BinaryCarrier n hn)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ A)
    (σ : CoefficientAut (binaryParameters n hn)) (hσ : orderOf σ = p)
    (hb : orderOf (coefficientAction _ σ) = p)
    (hbA : coefficientAction _ σ ∈ A)
    (hout : coefficientAction _ σ ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    3 ≤ primeRank p A := by
  obtain ⟨E, hE, hcard, hfix⟩ := exists_fixed_elementary n hn hpgt hd σ hσ
  let := hE
  let b := coefficientAction (binaryParameters n hn) σ
  let f : BinaryCarrier n hn →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect)
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨b, hbA⟩
  have hx : orderOf x = p :=
    (orderOf_injective A.subtype A.subtype_injective x).symm.trans hb
  have hxB : x ∉ B := by
    rintro ⟨g, _, he⟩
    exact hout ⟨g, congrArg Subtype.val he⟩
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * b y * g⁻¹ = b (g * y * g⁻¹)
    rw [map_mul, map_mul, map_inv, hgfix]
  have hcB : Nat.card B = p ^ 2 := by rw [card_map_of_injective hf, hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every prime actor at a cyclotomic prime is inner in a rank-two
full-inner automorphism overgroup of the genuine triality model. -/
theorem prime_actor_inner (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {p : ℕ} [Fact p.Prime] (hpgt : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (A : Subgroup (MulAut (BinaryCarrier n hn)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut (BinaryCarrier n hn)) (haA : a ∈ A)
    (ha : a ^ p = 1) : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn) := by
  by_contra hout
  have haorder : orderOf a = p := orderOf_eq_prime ha
    (fun he => hout (he ▸ (MulAut.innerSubgroup _).one_mem))
  let φ := coefficientAction (binaryParameters n hn)
  have hfaithful : Function.Injective
      ((QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))).comp φ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    exact (EvenField.NormalForm.coefficientAction_mem_inner_iff n hn σ).mp
      ((QuotientGroup.eq_one_iff _).mp hσ)
  obtain ⟨g, σ, _, hσ, hσA, hb, houter⟩ := MulAut.exists_prime_coefficient_in_overgroup
    φ hfaithful (Coverage.binary_inner_coefficient n hn) A hinner a haA haorder hout
  have hh := field_actor_rank_three n hn hpgt hd A hinner σ hσ hb hσA houter
  omega

end TrialityCyclotomic

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
