module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.SmallRows
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M12.Properties.AutCover

/-!
# The last four rows exclude the remaining bounded actors

In F.6.18(10)–(11), the actual special or projective degree-three group
contributes the cube of its odd defining prime. The literal index-two graph
extension preserves this divisor. No bounded binary rank-one actor has such
a divisor. For SL₃(4), SL₄(2), and S₈, an odd prime cube forces the prime to
be three; all three actors have a factor five, absent from SU₃(3), PSU₃(3),
and their index-two extensions. The calculation uses the actual central
quotient and the special/projective equivalence over the field of order nine.

In rows (12)–(13), M₁₂ contributes both 3³ and 11, the latter excluding all
three large actors. For Aut(M₁₂), its injective inner-automorphism map suffices.
Every comparison with the offender subgroup uses its literal inclusion in D
and the given two-group quotient D/N. No equality N = D or identification of
generalized Fitting subgroups is used. Both orientations and all clauses of
the source rows remain in the hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18(10–13),
pp.309–310, compared with B.5.1/B.5.6, pp.99–110, in 15.4.18, p.1163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open GoldschmidtAlternatives QuasisimpleComparison.ActorPruning
universe u v

private theorem card_sl_three_four (F : FFAlternatives.BinaryField) (hd : F.degree = 2) :
    Nat.card SL(3,F.Carrier) = 60480 := by
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
    Atlas.ExceptionalSupport.card_sl_center]
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F.Carrier) 3
  norm_num only [F.card_eq, hd, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_one, Fintype.card_fin] at h ⊢
  change Nat.card PSL(3,F.Carrier) * 3 = 60480
  omega

private theorem card_sl_four_two : Nat.card SL(4,ZMod 2) = 20160 := by
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(4,ZMod 2)),
    Atlas.ExceptionalSupport.card_sl_center]
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_one, Fintype.card_fin] at h ⊢
  exact h

private theorem prime_divisor_small {p n : ℕ} (hp : p.Prime)
    (hn : n = 60480 ∨ n = 20160 ∨ n = 40320) (hd : p ^ 3 ∣ n) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hd' : p ∣ n := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hm : n ∣ 2 ^ 7 * 3 ^ 3 * 5 * 7 := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hp' := hd'.trans hm
  simpa only [hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by decide : (7 : ℕ) ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : (3 : ℕ) ≠ 0), Nat.prime_dvd_prime_iff_eq hp
    (by decide : Nat.Prime 2), Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_assoc] using hp'

private theorem large_cube {A : Type*} [Group A] (ha : LargeActorModel A)
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) (hd : p ^ 3 ∣ Nat.card A) :
    p = 3 ∧ 5 ∣ Nat.card A := by
  have hc : Nat.card A = 60480 ∨ Nat.card A = 20160 ∨ Nat.card A = 40320 := by
    cases ha with
    | linearThreeFour F hF e =>
      exact Or.inl ((Nat.card_congr e.toEquiv).trans (card_sl_three_four F hF))
    | linearFourTwo e =>
      exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans card_sl_four_two))
    | symmetricEight e =>
      apply Or.inr ∘ Or.inr
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hp' := prime_divisor_small hp hc hd
  have hp3 : p = 3 := by
    rcases hp' with rfl | h | rfl | rfl
    · exact (hne rfl).elim
    · exact h
    · rcases hc with h | h | h <;> rw [h] at hd <;> norm_num at hd
    · rcases hc with h | h | h <;> rw [h] at hd <;> norm_num at hd
  refine ⟨hp3, ?_⟩
  rcases hc with h | h | h <;> rw [h] <;> norm_num

private theorem large_not_eleven {A : Type*} [Group A] (ha : LargeActorModel A) :
    ¬ 11 ∣ Nat.card A := by
  cases ha with
  | linearThreeFour F hF e => rw [Nat.card_congr e.toEquiv, card_sl_three_four F hF]; norm_num
  | linearFourTwo e => rw [Nat.card_congr e.toEquiv, card_sl_four_two]; norm_num
  | symmetricEight e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem unitary_three_card {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hc : Nat.card F = 3 ^ 2) (hf : ∀ x, J.conj x = x ^ 3) :
    Nat.card J.specialSubgroup = 6048 ∧
      Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = 6048 := by
  have hfixed : Nat.card {x : F // J.conj x = x} = 3 := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 3 1 (by decide)
        (by simpa using hc) (by simpa using hf)
  have hp := Representation.SU3.BinaryDegree.card_projective J hc hfixed
  norm_num only at hp
  refine ⟨?_, hp⟩
  rw [Nat.card_congr (J.specialProjectiveEquivOfCardNine (by simpa using hc)).toEquiv, hp]

private theorem extensionBy_card {D A : Type*} [Group D] [Group A]
    {a : MulAut A} (h : ExtensionBy D a) : Nat.card D = Nat.card A * 2 := by
  obtain ⟨i, t, hi, hindex, _, _⟩ := h
  rw [← i.range.card_mul_index, hindex,
    ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]

private theorem extensionBy_dvd {D A : Type*} [Group D] [Group A]
    {a : MulAut A} (h : ExtensionBy D a) {m : ℕ} (hd : m ∣ Nat.card A) :
    m ∣ Nat.card D := by
  rw [extensionBy_card h]
  exact dvd_mul_of_dvd_left hd _

private theorem linear_cube {D : Type*} [Group D] {p : ℕ}
    (h : LinearThree D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, hc, h | h⟩ := h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card.trans
      (card_dvd_of_surjective (QuotientGroup.mk' (center SL(3,F)))
        (QuotientGroup.mk'_surjective _))
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card

private theorem unitary_cube {D : Type*} [Group D] {p : ℕ} (hp : p.Prime)
    (h : UnitaryThree D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, h | h⟩ := h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_special hp hc hf
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective hp hc hf

private theorem unitary_not_five {D : Type*} [Group D]
    (h : UnitaryThree D 3) : ¬ 5 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, h | h⟩ := h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, (unitary_three_card J hc hf).1]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, (unitary_three_card J hc hf).2]
    norm_num

private theorem linearGraph_cube {D : Type*} [Group D] {p : ℕ}
    (h : LinearGraphExtension D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, hc, h | h⟩ := h
  · exact extensionBy_dvd h (linear_cube ⟨F, inferInstance, inferInstance, hc,
      Or.inl ⟨MulEquiv.refl _⟩⟩)
  · exact extensionBy_dvd h (linear_cube ⟨F, inferInstance, inferInstance, hc,
      Or.inr ⟨MulEquiv.refl _⟩⟩)

private theorem unitaryGraph_cube {D : Type*} [Group D] {p : ℕ} (hp : p.Prime)
    (h : UnitaryGraphExtension D p) : p ^ 3 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, hJ, h | h⟩ := h
  · exact extensionBy_dvd h (J.prime_cube_dvd_card_special hp hc hf)
  · exact extensionBy_dvd h (J.prime_cube_dvd_card_projective hp hc hf)

private theorem unitaryGraph_not_five {D : Type*} [Group D]
    (h : UnitaryGraphExtension D 3) : ¬ 5 ∣ Nat.card D := by
  obtain ⟨F, _, _, J, hc, hf, hJ, h | h⟩ := h
  · rw [extensionBy_card h, (unitary_three_card J hc hf).1]
    norm_num
  · rw [extensionBy_card h, (unitary_three_card J hc hf).2]
    norm_num

private def LastRowsOrder (D : Type*) : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ 3 ∣ Nat.card D ∧
    (p = 3 → ¬ 5 ∣ Nat.card D)) ∨ (3 ^ 3 ∣ Nat.card D ∧ 11 ∣ Nat.card D)

private theorem ordered_lastRows_order {D : Type*} [Group D]
    {G₁ G₂ : Subgroup D} (hr : LargeRowsOrdered G₁ G₂) : LastRowsOrder D := by
  rcases hr with h | h | h | h
  · obtain ⟨p, hp, ⟨hm, hl⟩ | ⟨hm, hu⟩, _⟩ := h
    · exact Or.inl ⟨p, hp, by omega, linear_cube hl, by intro he; omega⟩
    · refine Or.inl ⟨p, hp, by omega, unitary_cube hp hu, ?_⟩
      rintro rfl
      exact unitary_not_five hu
  · obtain ⟨p, hp, ⟨hm, hl⟩ | ⟨hm, hu⟩, _⟩ := h
    · exact Or.inl ⟨p, hp, by omega, linearGraph_cube hl, by intro he; omega⟩
    · refine Or.inl ⟨p, hp, by omega, unitaryGraph_cube hp hu, ?_⟩
      rintro rfl
      exact unitaryGraph_not_five hu
  · obtain ⟨⟨e⟩, _⟩ := h
    apply Or.inr
    rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]
    norm_num
  · obtain ⟨⟨e⟩, _⟩ := h
    have hd : Nat.card Sporadic.Mathieu.M12 ∣ Nat.card D := by
      rw [Nat.card_congr e.toEquiv]
      exact card_dvd_of_injective Sporadic.Mathieu.m12InnerAut
        Sporadic.Mathieu.m12InnerAut_injective
    rw [Sporadic.Mathieu.m12_order] at hd
    exact Or.inr ⟨(by norm_num : 3 ^ 3 ∣ 95040).trans hd,
      (by norm_num : 11 ∣ 95040).trans hd⟩

variable {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}

/-- The complete last-four-row comparison for the bounded offender branch.
Odd divisors are transported through the actual quotient D/N. The retained
G₂(2)′ and G₂(2) actors are outside the two excluded families. -/
theorem ProjectiveLine.ClassifiedAction.lastRows_not_remainingActors
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (_b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    LargeRows G₁ G₂ →
      (¬ RankOneActorModel (offenderSubgroup ρ)) ∧
      (¬ LargeActorModel (offenderSubgroup ρ)) := by
  intro hr
  have hd : LastRowsOrder D := by
    rcases hr with hr | hr <;> exact ordered_lastRows_order hr
  constructor
  · intro ha
    rcases hd with ⟨p, hp, hne, hcube, _⟩ | ⟨hcube, _⟩
    · exact h.rankOne_not_odd_prime_cube ha hp hne hcube
    · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide) hcube
  · intro ha
    rcases hd with ⟨p, hp, hne, hcube, hnot⟩ | ⟨_, heleven⟩
    · have hcube' := (h.odd_dvd_offender_card_iff ((hp.odd_of_ne_two hne).pow)).mpr hcube
      obtain ⟨he, hfive⟩ := large_cube ha hp hne hcube'
      exact hnot he ((h.odd_dvd_offender_card_iff (by decide : Odd 5)).mp hfive)
    · exact large_not_eleven ha
        ((h.odd_dvd_offender_card_iff (by decide : Odd 11)).mpr heleven)
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
