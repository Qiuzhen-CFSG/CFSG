module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.Models
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M12.Properties.AutCover

/-!
# The actual last four F.6.18 rows exclude the remaining actors

The degree-three models contribute the cube of their odd defining prime.
In the three large bounded actors this forces the prime to be three, whereas
the source sign condition then forces the unitary model, whose order lacks
five. The actual external normalizing involution doubles the component order
in the graph row. The Mathieu rows contribute both 27 and 11, using the
injective inner-automorphism map for the automorphism group.

Odd divisors pass through the literal normal subgroup and its two-group
quotient. Thus the comparisons apply to the actual offender subgroup without
identifying it with the ambient group. Source fields retain their universe,
Frobenius action, sign condition, and actual special/projective quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18(10–13), pp.309–310, and its use in 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open QuasisimpleComparison.ActorPruning
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u

/-- The actual ambient models in corrected source rows (10)–(13). -/
def LargeRow (D : Type u) [Group D] [Finite D] : Prop :=
  (∃ p, p.Prime ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ FSource.DegreeThree p D) ∨
  Nonempty (FSource.GraphExtensionRow (D := D)) ∨
  Nonempty (D ≃* Sporadic.Mathieu.M12) ∨
  Nonempty (D ≃* MulAut Sporadic.Mathieu.M12)

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

private theorem degreeThree_three_card {D : Type u} [Group D]
    (h : FSource.DegreeThree 3 D) : Nat.card D = 6048 := by
  cases h with
  | linear _ _ hs _ => norm_num at hs
  | projectiveLinear _ _ hs _ => norm_num at hs
  | unitary _ J hc hf _ e =>
    exact (Nat.card_congr e.toEquiv).trans (unitary_three_card J hc hf).1
  | projectiveUnitary _ J hc hf _ e =>
    exact (Nat.card_congr e.toEquiv).trans (unitary_three_card J hc hf).2

private theorem graphExtension_card {D : Type u} [Group D] [Finite D]
    (r : FSource.GraphExtensionRow (D := D)) :
    Nat.card D = 2 * Nat.card (generalizedFitting D) := by
  have hw : r.element ^ 2 = 1 := by
    rw [← r.involution]
    exact pow_orderOf_eq_one r.element
  have hnorm : r.element ∈ Subgroup.normalizer (generalizedFitting D : Set D) := by
    rw [(generalizedFitting D).normalizer_eq_top]
    trivial
  have hc := card_sup_zpowers_of_normalizing_involution
    (generalizedFitting D) r.element hw r.outside hnorm
  simpa only [r.generated, card_top] using hc

private def LastRowsOrder (D : Type*) : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ 3 ∣ Nat.card D ∧
    (p = 3 → ¬ 5 ∣ Nat.card D)) ∨ (3 ^ 3 ∣ Nat.card D ∧ 11 ∣ Nat.card D)

private theorem largeRow_order {D : Type u} [Group D] [Finite D]
    (r : LargeRow D) : LastRowsOrder D := by
  rcases r with h | h | h | h
  · obtain ⟨p, hp, hmod, hm⟩ := h
    refine Or.inl ⟨p, hp, by omega, degreeThree_prime_cube hp hm, ?_⟩
    rintro rfl
    rw [degreeThree_three_card hm]
    norm_num
  · obtain ⟨r⟩ := h
    have hc := (degreeThree_prime_cube r.prime_isPrime r.model.model).trans
      (generalizedFitting D).card_subgroup_dvd_card
    have hne : r.prime ≠ 2 := by have := r.congruence; omega
    refine Or.inl ⟨r.prime, r.prime_isPrime, hne, hc, ?_⟩
    intro hp
    have hm : FSource.DegreeThree 3 (generalizedFitting D) := hp ▸ r.model.model
    rw [graphExtension_card r, degreeThree_three_card hm]
    norm_num
  · obtain ⟨e⟩ := h
    apply Or.inr
    rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]
    norm_num
  · obtain ⟨e⟩ := h
    have hd : Nat.card Sporadic.Mathieu.M12 ∣ Nat.card D := by
      rw [Nat.card_congr e.toEquiv]
      exact card_dvd_of_injective Sporadic.Mathieu.m12InnerAut
        Sporadic.Mathieu.m12InnerAut_injective
    rw [Sporadic.Mathieu.m12_order] at hd
    exact Or.inr ⟨(by norm_num : 3 ^ 3 ∣ 95040).trans hd,
      (by norm_num : 11 ∣ 95040).trans hd⟩

private theorem odd_dvd_normal_iff {D : Type u} [Group D] [Finite D]
    (N : Subgroup D) [N.Normal] (hquot : IsPGroup 2 (D ⧸ N))
    {m : ℕ} (hm : Odd m) : m ∣ Nat.card N ↔ m ∣ Nat.card D := by
  constructor
  · exact fun hd => hd.trans N.card_subgroup_dvd_card
  · intro hd
    obtain ⟨k, hk⟩ := hquot.exists_card_eq
    have he : Nat.card D = Nat.card N * 2 ^ k := by
      rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
    rw [he] at hd
    exact ((Nat.coprime_two_right.mpr hm).pow_right k).dvd_of_dvd_mul_right hd

/-- None of the four actual large source rows admits either remaining bounded
actor as a normal subgroup with two-group quotient. This applies directly to
the offender subgroup of the original action. -/
theorem largeRow_not_remainingActors {D : Type u} [Group D] [Finite D]
    (N : Subgroup D) [N.Normal] (hquot : IsPGroup 2 (D ⧸ N))
    (r : LargeRow D) : (¬ RankOneActorModel N) ∧ (¬ LargeActorModel N) := by
  have hd := largeRow_order r
  constructor
  · intro ha
    rcases hd with ⟨p, hp, hne, hcube, _⟩ | ⟨hcube, _⟩
    · exact ha.not_odd_prime_cube hp hne
        ((odd_dvd_normal_iff N hquot (hp.odd_of_ne_two hne).pow).mpr hcube)
    · exact ha.not_odd_prime_cube (by decide : Nat.Prime 3) (by decide)
        ((odd_dvd_normal_iff N hquot (by decide : Odd (3 ^ 3))).mpr hcube)
  · intro ha
    rcases hd with ⟨p, hp, hne, hcube, hnot⟩ | ⟨_, heleven⟩
    · have hcube' := (odd_dvd_normal_iff N hquot (hp.odd_of_ne_two hne).pow).mpr hcube
      obtain ⟨he, hfive⟩ := large_cube ha hp hne hcube'
      exact hnot he ((odd_dvd_normal_iff N hquot (by decide : Odd 5)).mp hfive)
    · exact large_not_eleven ha
        ((odd_dvd_normal_iff N hquot (by decide : Odd 11)).mpr heleven)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
