module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.SmallOrders
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearTwoSylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearThreeBound
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Excluding the odd-prime product row F.6.18(3)

An ambient Sylow of order eight restricts the binary SL₂ factors to fields
of order at most eight, and the odd-degree SL₃ factors to the binary field.
Each actual factor order therefore divides 2520. A two-group quotient adds
no odd prime to the group order. The nonsplit A₆–C₃ branch likewise has
no prime greater than five, because generation by binary offenders makes
the cyclic quotient over its literal product a two-group.

F.6.18(3) contains PSL₂(p), where p is prime and p is 11 or 13 modulo 24.
That prime divides the ambient order, contradicting the preceding prime
support calculation. The proof uses the actual common Sylow subgroup and
works with the literal offender subgroup, even when it is proper.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3)–(5), pp.105–110; F.6.18(3), p.309; 15.4.18, p.1163.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison
open FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
variable {D : Type*} [Group D] [Finite D]

private theorem embedded_sylow_card_le {A : Type*} [Group A]
    (f : A →* D) (hf : Function.Injective f) (P : Sylow 2 A) (S : Sylow 2 D) :
    Nat.card P ≤ Nat.card S := by
  obtain ⟨R,hR⟩ := (P.isPGroup'.map f).exists_le_sylow
  have hh := (card_le_of_le hR).trans (Nat.card_congr (R.equiv S).toEquiv).le
  rwa [card_map_of_injective hf] at hh

/-- Under the order-eight ambient Sylow bound, every actual B.5.6 factor
has order dividing 2520. Only the primes 2, 3, 5 and 7 can occur. -/
theorem factor_card_dvd_of_sylow_eight {A : Type*} [Group A]
    (h : FactorModel A) (f : A →* D) (hf : Function.Injective f)
    (S : Sylow 2 D) (hS : Nat.card S ≤ 8) : Nat.card A ∣ 2520 := by
  cases h with
  | linearTwo F e =>
    let P : Sylow 2 SL(2,F.Carrier) := default
    have hh := (embedded_sylow_card_le (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) P S).trans hS
    rw [linearTwo_sylow_card F P] at hh
    have hn : F.degree ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    have hp := F.degree_pos
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, F.card_eq]
    interval_cases hd : F.degree <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  | linearThree F ho e =>
    have hn := linearThree_degree_eq_one F ho (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) S (hS.trans (by decide))
    let : Fintype F.Carrier := Fintype.ofFinite _
    let a : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, F.card_eq, hn]
      simp)
    rw [Nat.card_congr (e.trans (Atlas.fieldEquivSL 3 a)).toEquiv, Matrix.PSL3Two.card_SL]
    decide

private theorem not_large_prime_dvd_2520 {p : ℕ} (hp : p.Prime) (hlarge : 7 < p) : ¬ p ∣ 2520 := by
  intro hd
  rw [show (2520 : ℕ) = 2^3 * 3^2 * 5 * 7 by decide] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow hd)
        omega
      · have := Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow hd)
        omega
    · have := Nat.le_of_dvd (by decide : 0 < 5) hd
      omega
  · have := Nat.le_of_dvd (by decide : 0 < 7) hd
    omega

private theorem odd_prime_dvd_normal (N : Subgroup D) [N.Normal]
    (hq : IsPGroup 2 (D ⧸ N)) {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (hd : p ∣ Nat.card D) : p ∣ Nat.card N := by
  obtain ⟨k,hk⟩ := hq.exists_card_eq
  have he : Nat.card D = Nat.card N * 2^k := by
    rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have hh := hp.dvd_of_dvd_pow hd
    exact (hne ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hh |>.resolve_left hp.ne_one)).elim

private theorem product_not_large_prime {N : Subgroup D} {A B : Subgroup N}
    (c : InternalProduct A B) (ha : FactorModel A) (hb : FactorModel B)
    (S : Sylow 2 D) (hS : Nat.card S ≤ 8) {p : ℕ} (hp : p.Prime) (hlarge : 7 < p) :
    ¬ p ∣ Nat.card N := by
  intro hd
  rw [← Nat.card_congr c.equiv.toEquiv, Nat.card_prod] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact not_large_prime_dvd_2520 hp hlarge (hd.trans
      (factor_card_dvd_of_sylow_eight ha (N.subtype.comp A.subtype)
        (N.subtype_injective.comp A.subtype_injective) S hS))
  · exact not_large_prime_dvd_2520 hp hlarge (hd.trans
      (factor_card_dvd_of_sylow_eight hb (N.subtype.comp B.subtype)
        (N.subtype_injective.comp B.subtype_injective) S hS))

universe u v
variable {E : Type u} [Group E] [Finite E]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) E V} {G₁ G₂ : Subgroup E} {K : GroupClass.{u}}
attribute [local instance] offenderSubgroup_normal

/-- With an ambient Sylow of order at most eight, all three branches have
no prime divisor greater than seven, including the possible ambient extension. -/
theorem branch_not_large_prime (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))
    (S : Sylow 2 E) (hS : Nat.card S ≤ 8) {p : ℕ} (hp : p.Prime) (hlarge : 7 < p) :
    ¬ p ∣ Nat.card E := by
  intro hd
  have hN := odd_prime_dvd_normal (offenderSubgroup ρ) h.quotient_twoGroup hp (by omega) hd
  unfold Branch at hb
  rcases hb with hb | hb | hb <;> obtain ⟨hb⟩ := hb
  · exact product_not_large_prime hb.product
      (hb.firstCase.factorModel _) (hb.secondCase.factorModel _) S hS hp hlarge hN
  · let := hb.product_normal
    let := hb.quotient_isCyclic
    let := IsCyclic.commGroup (α := offenderSubgroup ρ ⧸ (hb.first ⊔ hb.second))
    have hq := abelian_image_isTwoGroup _ (QuotientGroup.mk' (hb.first ⊔ hb.second))
      (QuotientGroup.mk'_surjective _) h.ffHypothesis.generated
    have hprod := odd_prime_dvd_normal (hb.first ⊔ hb.second) hq hp (by omega) hN
    have hcard : Nat.card (hb.first ⊔ hb.second : Subgroup (offenderSubgroup ρ)) = 1080 := by
      rw [← Nat.card_congr hb.product.toEquiv, Nat.card_prod,
        Nat.card_congr hb.firstEquiv.toEquiv, Nat.card_congr hb.secondEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcard] at hprod
    have hh : p ∣ 2520 * 3 := hprod.trans (by decide : 1080 ∣ 2520 * 3)
    rcases hp.dvd_mul.mp hh with hh | hh
    · exact not_large_prime_dvd_2520 hp hlarge hh
    · have := Nat.le_of_dvd (by decide : 0 < 3) hh
      omega
  · exact product_not_large_prime hb.product
      (.linearThree BinaryField.two (by decide) hb.firstEquiv)
      (hb.secondCase.factorModel _) S hS hp hlarge hN

private theorem psl_prime_dvd {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hm : ClassicalGroup.IsPSL A 2 p) : p ∣ Nat.card A := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  have hd : p ∣ Nat.card PSL(2,F) * 2 := by
    rw [hc, hF]
    exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have he := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hp.ne_one
    have hh := Nat.odd_iff.mp ho
    omega

/-- Complete exclusion of F.6.18(3) for these branches, retaining the exact
prime congruence, ambient two-group extension and common Sylow subgroup. -/
theorem not_case3 (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ GoldschmidtAlternatives.Case3 G₁ G₂ := by
  rintro ⟨p,A,B,hp,hm,hA,_,_,_,_,⟨e⟩,_⟩
  have hd : p ∣ Nat.card E := (psl_prime_dvd hp (Nat.odd_iff.mpr (by omega)) hA).trans
    A.card_subgroup_dvd_card
  obtain ⟨S,hS⟩ := h.triple.intersection_sylow
  have hc : Nat.card S ≤ 8 := by
    rw [← Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact branch_not_large_prime h hb S hc hp (by omega) hd

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
