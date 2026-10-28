module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Basic
public import GorensteinWalter.PGL2Cardinality
/-!
# Excluding rank-one actors in the complete low source rows

Sylow orders and odd divisors compare every early Goldschmidt row with
the bounded rank-one offender models. This includes arbitrary source fields
and both corrected extensions. In the square-field characteristic-five
case, the divisor thirteen excludes the remaining rank-one possibilities.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open QuasisimpleComparison.ActorPruning FFAlternatives
namespace RankOneRows
variable {D : Type*} [Group D] [Finite D] {A : Type*} [Group A]
private theorem linear_degree_bound (F : BinaryField) (i : SL(2,F.Carrier) →* D)
    (hi : Function.Injective i) (S : Sylow 2 D) {k : ℕ} (hs : Nat.card S ≤ 2 ^ k) :
    F.degree ≤ k := by
  have hd : 2 ^ F.degree ∣ Nat.card SL(2,F.Carrier) := by
    rw [GorensteinWalter.sl2_card_formula, F.card_eq]
    exact dvd_mul_right _ _
  have hb := S.pow_dvd_card_of_pow_dvd_card
    (hd.trans (card_dvd_of_injective i hi))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.le_of_dvd (Nat.card_pos (α := S)) hb).trans hs)

private theorem card_cases_eight (ha : RankOneActorModel A)
    (i : A →* D) (hi : Function.Injective i) (S : Sylow 2 D) (hs : Nat.card S ≤ 8) :
    Nat.card A = 60 ∨ Nat.card A = 120 ∨ Nat.card A = 504 := by
  cases ha with
  | linearTwo F hlo _ e =>
    have hn := linear_degree_bound F (i.comp e.symm.toMonoidHom)
      (hi.comp e.symm.injective) S (k := 3) hs
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem card_cases_sixteen (ha : RankOneActorModel A)
    (i : A →* D) (hi : Function.Injective i) (S : Sylow 2 D) (hs : Nat.card S ≤ 16) :
    Nat.card A = 60 ∨ Nat.card A = 120 ∨ Nat.card A = 504 ∨ Nat.card A = 4080 := by
  cases ha with
  | linearTwo F hlo _ e =>
    have hn := linear_degree_bound F (i.comp e.symm.toMonoidHom)
      (hi.comp e.symm.injective) S (k := 4) hs
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem prime_support_eight {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : n = 60 ∨ n = 120 ∨ n = 504) (hd : p ∣ n) : p = 3 ∨ p = 5 ∨ p = 7 := by
  have hd' : p ∣ 2 * 2 * 2 * 3 * 3 * 5 * 7 := hd.trans (by
    rcases hc with rfl | rfl | rfl <;> norm_num)
  have hne : p ≠ 2 := by intro h; subst p; norm_num at ho
  simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    hne, false_or, or_assoc, or_self_left] using hd'

private theorem prime_support_sixteen {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : n = 60 ∨ n = 120 ∨ n = 504 ∨ n = 4080) (hd : p ∣ n) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
  have hd' : p ∣ 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 * 17 := hd.trans (by
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num)
  have hne : p ≠ 2 := by intro h; subst p; norm_num at ho
  simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
    hne, false_or, or_assoc, or_self_left] using hd'

private theorem not_dvd_small_orders (ha : RankOneActorModel A) {m : ℕ}
    (hm : m = 36 ∨ m = 108 ∨ m = 168) : ¬ Nat.card A ∣ m := by
  cases ha with
  | linearTwo F hlo hhi e =>
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> rcases hm with rfl | rfl | rfl <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    rcases hm with rfl | rfl | rfl <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem psl_card_twice {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (e : A ≃* PSL(2,F)) :
    Nat.card A * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho

private theorem psl_field_dvd {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (e : A ≃* PSL(2,F)) : Nat.card F ∣ Nat.card A := by
  apply (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_right
  rw [psl_card_twice ho e]
  exact dvd_mul_right _ _

private theorem triple_alternating_cube {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hc : FSource.TripleAlternating A n) : 27 ∣ Nat.card A := by
  rw [card_eq_card_quotient_mul_card_subgroup (center A),
    Nat.card_congr hc.center.some.toEquiv,Nat.card_congr hc.quotient.some.toEquiv]
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [FSource.C,Nat.factorial]

private theorem triple_symmetric_cube {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hc : FSource.TripleSymmetric A n) : 27 ∣ Nat.card A := by
  let := hc.normal
  rw [card_eq_card_quotient_mul_card_subgroup hc.kernel,
    Nat.card_congr hc.kernelEquiv.toEquiv,Nat.card_congr hc.quotientEquiv.toEquiv]
  rcases hn with rfl | rfl <;>
    norm_num [FSource.C,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

universe u v
variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal
private theorem prime_eight (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 8)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card D) :
    p = 3 ∨ p = 5 ∨ p = 7 :=
  prime_support_eight hp ho (card_cases_eight ha (offenderSubgroup ρ).subtype
    Subtype.val_injective S hs) ((h.odd_dvd_offender_card_iff ho).mpr hd)

private theorem prime_sixteen (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card D) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 :=
  prime_support_sixteen hp ho (card_cases_sixteen ha (offenderSubgroup ρ).subtype
    Subtype.val_injective S hs) ((h.odd_dvd_offender_card_iff ho).mpr hd)

private theorem not_odd_product (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16)
    {m : ℕ} (hm : m = 35 ∨ m = 45) : ¬ m ∣ Nat.card D := by
  intro hd
  have ho : Odd m := by rcases hm with rfl | rfl <;> decide
  have hn := (h.odd_dvd_offender_card_iff ho).mpr hd
  rcases card_cases_sixteen ha (offenderSubgroup ρ).subtype Subtype.val_injective S hs
    with hc | hc | hc | hc <;> rw [hc] at hn <;>
    rcases hm with rfl | rfl <;> norm_num at hn


private theorem not_dihedral (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (F : FSource.FieldParameter.{u}) (hn : F.degree ≤ 2)
    (hm : Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9)
    (e : D ≃* PSL(2,F.Carrier)) (S : Sylow 2 D) (hs : Nat.card S ≤ 8) : False := by
  have hp := F.prime_isPrime
  have hnpos := F.degree_pos
  have hp2 : F.prime ≠ 2 := by
    intro he
    rw [F.card,he] at hm
    interval_cases F.degree <;> norm_num at hm
  have ho := hp.odd_of_ne_two hp2
  have hFo : Odd (Nat.card F.Carrier) := F.card ▸ ho.pow
  have hd : F.prime ∣ Nat.card D :=
    (dvd_pow_self F.prime (by omega : F.degree ≠ 0)).trans
      (F.card ▸ psl_field_dvd hFo e)
  have hh := prime_eight h ha S hs hp ho hd
  have hm' := hm
  rw [F.card] at hm'
  rcases hh with hp3 | hp5 | hp7
  · rw [hp3] at hm'
    interval_cases hd : F.degree <;> norm_num at hm'
    have hh := psl_card_twice hFo e
    rw [F.card,hp3,hd] at hh
    have hc : Nat.card D = 360 := by norm_num at hh; omega
    exact not_odd_product h ha S (hs.trans (by decide)) (Or.inr rfl)
      (by rw [hc]; decide)
  · rw [hp5] at hm'
    interval_cases hd : F.degree <;> norm_num at hm'
    have hh := psl_card_twice hFo e
    rw [F.card,hp5,hd] at hh
    have hc : Nat.card D = 7800 := by norm_num at hh; omega
    have hx := prime_eight h ha S hs (by decide : Nat.Prime 13)
      (by decide : Odd 13) (by rw [hc]; decide)
    norm_num at hx
  · rw [hp7] at hm'
    interval_cases hd : F.degree <;> norm_num at hm'
    have hh := psl_card_twice hFo e
    rw [F.card,hp7,hd] at hh
    have hc : Nat.card D = 168 := by norm_num at hh; omega
    exact not_dvd_small_orders ha (Or.inr (Or.inr hc))
      (offenderSubgroup ρ).card_subgroup_dvd_card

private theorem not_square_field (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (F : FSource.FieldParameter.{u}) (hn : F.degree = 2)
    (hm : F.prime % 8 = 3 ∨ F.prime % 8 = 5)
    (i : PSL(2,F.Carrier) →* D) (hi : Function.Injective i)
    (S : Sylow 2 D) (hs : Nat.card S ≤ 16) : False := by
  have hp := F.prime_isPrime
  have ho : Odd F.prime := Nat.odd_iff.mpr (by omega)
  have hFo : Odd (Nat.card F.Carrier) := by rw [F.card,hn]; exact ho.pow
  have hd : F.prime ∣ Nat.card D :=
    (dvd_pow_self F.prime (by decide : 2 ≠ 0)).trans
      ((show F.prime ^ 2 ∣ Nat.card PSL(2,F.Carrier) by
        simpa only [F.card,hn] using psl_field_dvd hFo (MulEquiv.refl PSL(2,F.Carrier))).trans
        (card_dvd_of_injective i hi))
  have hh := prime_sixteen h ha S hs hp ho hd
  have he : F.prime = 3 ∨ F.prime = 5 := by omega
  rcases he with hp3 | hp5
  · have hh := psl_card_twice hFo (MulEquiv.refl PSL(2,F.Carrier))
    rw [F.card,hn,hp3] at hh
    have hc : Nat.card PSL(2,F.Carrier) = 360 := by norm_num at hh; omega
    exact not_odd_product h ha S hs (Or.inr rfl)
      ((show 45 ∣ Nat.card PSL(2,F.Carrier) by rw [hc]; decide).trans
        (card_dvd_of_injective i hi))
  · have hh := psl_card_twice hFo (MulEquiv.refl PSL(2,F.Carrier))
    rw [F.card,hn,hp5] at hh
    have hc : Nat.card PSL(2,F.Carrier) = 7800 := by norm_num at hh; omega
    have hx := prime_sixteen h ha S hs (by decide : Nat.Prime 13)
      (by decide : Odd 13) ((show 13 ∣ Nat.card PSL(2,F.Carrier) by rw [hc]; decide).trans
        (card_dvd_of_injective i hi))
    norm_num at hx

private theorem not_prime_psl (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (F : FSource.FieldParameter.{u}) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (i : PSL(2,F.Carrier) →* D) (hi : Function.Injective i)
    (S : Sylow 2 D) (hs : Nat.card S ≤ 8) : False := by
  have ho : Odd F.prime := Nat.odd_iff.mpr (by omega)
  have hc : Nat.card F.Carrier = F.prime := by rw [F.card,hn,pow_one]
  have hd : F.prime ∣ Nat.card D :=
    (hc ▸ psl_field_dvd (hc ▸ ho) (MulEquiv.refl PSL(2,F.Carrier))).trans
      (card_dvd_of_injective i hi)
  have hh := prime_eight h ha S hs F.prime_isPrime ho hd
  omega

private theorem not_alternating_seven (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (e : D ≃* alternatingGroup (Fin 7)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16) : False := by
  exact not_odd_product h ha S hs (Or.inl rfl) (by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num [Nat.factorial])

private theorem not_symmetric_seven (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (e : D ≃* Equiv.Perm (Fin 7)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16) : False := by
  exact not_odd_product h ha S hs (Or.inl rfl) (by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])

def EarlyAlternative {D : Type u} [Group D] [Finite D]
    (S : Sylow 2 D) : Prop :=
  (∃ F : FSource.FieldParameter.{u}, F.degree = 1 ∧
      (F.prime % 24 = 11 ∨ F.prime % 24 = 13) ∧
      ∃ i : PSL(2,F.Carrier) →* D, Function.Injective i ∧ Nat.card S ≤ 8) ∨
    FSource.TripleAlternating D 6 ∨ FSource.TripleAlternating D 7 ∨
    Nonempty (FSource.TripleSymmetric D 6) ∨ Nonempty (FSource.TripleSymmetric D 7) ∨
    (Nonempty (D ≃* alternatingGroup (Fin 7)) ∧ Nat.card S ≤ 16) ∨
    (Nonempty (D ≃* Equiv.Perm (Fin 7)) ∧ Nat.card S ≤ 16) ∨
    Nonempty (FSource.DihedralPSL2Row S) ∨ Nonempty (FSource.SquareFieldExtensionRow S)

theorem not_earlyAlternative (h : ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) {S : Sylow 2 D}
    (r : EarlyAlternative S) : False := by
  rcases r with ⟨F,hn,hm,i,hi,hs⟩ | r | r | r | r | ⟨r,hs⟩ | ⟨r,hs⟩ | r | r
  · exact not_prime_psl h ha F hn hm i hi S hs
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_alternating_cube (Or.inl rfl) r)
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_alternating_cube (Or.inr rfl) r)
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_symmetric_cube (Or.inl rfl) r.some)
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_symmetric_cube (Or.inr rfl) r.some)
  · exact not_alternating_seven h ha r.some S hs
  · exact not_symmetric_seven h ha r.some S hs
  · obtain ⟨r⟩ := r
    exact not_dihedral h ha r.field r.degree r.congruence r.model S (by
      rw [Nat.card_congr r.sylow.some.toEquiv,DihedralGroup.nat_card])
  · obtain ⟨r⟩ := r
    exact not_square_field h ha r.field r.degree r.congruence
      ((generalizedFitting D).subtype.comp r.componentEquiv.symm.toMonoidHom)
      (Subtype.val_injective.comp r.componentEquiv.symm.injective) S (by
        rw [Nat.card_congr r.sylow.some.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
        norm_num [FSource.C])

end RankOneRows
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
