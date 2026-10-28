module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Orders
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.Center

/-!
# The Mathieu-23 and Janko-4 exclusions in the FF comparison

The two-part of each field-family order fixes its field degree or gives
an immediate contradiction. The resulting orders and all finite endpoints
differ from M23 and J4. Thus neither concrete sporadic carrier occurs in
the full B.4/B.5 image list. Their proved centerlessness then identifies
the original two-core quotient with the literal action image, excluding
both original 11.1.1 rows without dropping any action kernel.

The private field-order calculations follow the checked A7 comparison in
AlternatingSeven/FieldWitness/Orders. The final chosen-flag applications
are in Classification.lean; no FF or classification premise remains there.
Source: Aschbacher--Smith 11.4.2, printed pp.776--777, and B.4.2/B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

open ChapterB.QuasisimpleSource

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem binary_sub_one_two_part {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((2 ^ n) ^ k - 1).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  have he : ((2 ^ n) ^ k) % 2 = 0 := by
    simp [Nat.pow_mod, Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  have hp : 0 < (2 ^ n) ^ k := by positivity
  omega

private theorem binary_sub_one_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < (2 ^ n) ^ k - 1 := by
  have h : 1 < (2 ^ n) ^ k :=
    one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by omega)
  omega

private theorem binary_order_two_part {n a b c : ℕ}
    (hn : 0 < n) (hb : 0 < b) (hc : 0 < c) :
    ((2 ^ n) ^ a * ((2 ^ n) ^ b - 1) * ((2 ^ n) ^ c - 1)).factorization 2 = a * n := by
  have hbpos := binary_sub_one_pos hn hb
  rw [Nat.factorization_mul (by positivity) (by
    exact Nat.ne_of_gt (binary_sub_one_pos hn hc)),
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hb))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part hn hb,
    binary_sub_one_two_part hn hc, add_zero]
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two, Nat.mul_comm]

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem sl_two_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).factorization 2 = F.degree := by
  rw [Atlas.card_sl_two, F.card_eq,
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos F.degree_pos (by decide)))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part F.degree_pos (by decide : 0 < 2),
    add_zero, Nat.factorization_pow_self Nat.prime_two]

private theorem sl_three_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)).factorization 2 = 3 * F.degree := by
  rw [sl_three_card, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sp_four_part (F : BinaryField) :
    (Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier)).factorization 2 = 4 * F.degree := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp F.Carrier, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem g2_part (F : BinaryField) :
    (Nat.card (Atlas.G2.Model F.Carrier)).factorization 2 = 6 * F.degree := by
  rw [Atlas.G2.card_Model, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sl_four_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  have h := sl_card_mul (ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem sl_five_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have h := sl_card_mul (ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem derived_g2_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

/-- The sporadic orders occurring as maximal proper overcomponent quotients. -/
private def SporadicOrder (N : ℕ) : Prop := N = 10200960 ∨ N = 86775571046077562880

private theorem not_sl_two_sporadic (F : BinaryField) {N : ℕ} (hN : SporadicOrder N) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) ≠ N := by
  intro h
  have hp := sl_two_part F
  rcases hN with rfl | rfl
  · rw [h, show Nat.factorization 10200960 2 = 7 by decide +kernel] at hp
    have hn : F.degree = 7 := hp.symm
    rw [Atlas.card_sl_two, F.card_eq, hn] at h
    norm_num at h
  · rw [h, show Nat.factorization 86775571046077562880 2 = 21 by decide +kernel] at hp
    have hn : F.degree = 21 := hp.symm
    rw [Atlas.card_sl_two, F.card_eq, hn] at h
    norm_num at h

private theorem not_sl_three_sporadic (F : BinaryField) {N : ℕ} (hN : SporadicOrder N) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) ≠ N := by
  intro h
  have hp := sl_three_part F
  rcases hN with rfl | rfl
  · rw [h, show Nat.factorization 10200960 2 = 7 by decide +kernel] at hp
    omega
  · rw [h, show Nat.factorization 86775571046077562880 2 = 21 by decide +kernel] at hp
    have hn : F.degree = 7 := by omega
    rw [sl_three_card, F.card_eq, hn] at h
    norm_num at h

private theorem not_sp_four_sporadic (F : BinaryField) {N : ℕ} (hN : SporadicOrder N) :
    Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) ≠ N := by
  intro h
  have hp := sp_four_part F
  rcases hN with rfl | rfl
  · rw [h, show Nat.factorization 10200960 2 = 7 by decide +kernel] at hp
    omega
  · rw [h, show Nat.factorization 86775571046077562880 2 = 21 by decide +kernel] at hp
    omega

private theorem not_g2_sporadic (F : BinaryField) {N : ℕ} (hN : SporadicOrder N) :
    Nat.card (Atlas.G2.Model F.Carrier) ≠ N := by
  intro h
  have hp := g2_part F
  rcases hN with rfl | rfl
  · rw [h, show Nat.factorization 10200960 2 = 7 by decide +kernel] at hp
    omega
  · rw [h, show Nat.factorization 86775571046077562880 2 = 21 by decide +kernel] at hp
    omega

/-- Neither sporadic overcomponent is a possible faithful FF component image. -/
private theorem not_image_model_of_sporadic_order {A : Type*} [Group A] [Finite A]
    (hN : SporadicOrder (Nat.card A)) : ¬ ImageModel A := by
  intro hm
  cases hm with
  | linearTwo F e => exact not_sl_two_sporadic F hN (Nat.card_congr e.toEquiv).symm
  | linearThree F e => exact not_sl_three_sporadic F hN (Nat.card_congr e.toEquiv).symm
  | symplectic F _ e => exact not_sp_four_sporadic F hN (Nat.card_congr e.toEquiv).symm
  | g2 F _ e => exact not_g2_sporadic F hN (Nat.card_congr e.toEquiv).symm
  | symplecticTwo e =>
    have hb := Nat.card_le_card_of_injective _
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
    rw [← Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp,
      Nat.card_zmod] at hb
    rcases hN with hN | hN <;> rw [hN] at hb <;> norm_num at hb
  | g2Two e =>
    have hc := (Nat.card_congr e.toEquiv).trans derived_g2_card
    rcases hN with hN | hN <;> omega
  | alternating n hn e =>
    have hc := Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup] at hc <;>
      norm_num [Nat.factorial] at hc <;> rcases hN with hN | hN <;> omega
  | tripleSix z e =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center A)
    rw [Nat.card_congr e.toEquiv, Nat.card_congr z.toEquiv,
      nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
    rcases hN with hN | hN <;> omega
  | binaryLinear n hn e =>
    have hc := Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl
    · rw [sl_four_card] at hc
      rcases hN with hN | hN <;> omega
    · rw [sl_five_card] at hc
      rcases hN with hN | hN <;> omega

/-- The negative Mathieu comparison uses the concrete Mathieu carrier. -/
theorem not_image_model_m23 : ¬ ImageModel Sporadic.Mathieu.M23 :=
  not_image_model_of_sporadic_order (Or.inl Sporadic.Mathieu.m23_order)

/-- The negative Janko comparison uses the original ATLAS matrix carrier. -/
theorem not_image_model_j4 : ¬ ImageModel Janko4.Model :=
  not_image_model_of_sporadic_order (Or.inr Janko4.Cardinality.model_card)

private theorem false_of_centerless_quotient_model
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E))
    {A : Type*} [Group A] (e : (E.Kz ⧸ pCore 2 E.Kz) ≃* A)
    (hz : center A = ⊥) (ha : ¬ ImageModel A) : False := by
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  have hzQ : center (E.Kz ⧸ pCore 2 E.Kz) = ⊥ := by
    apply bot_unique
    intro q hq
    apply mem_bot.mpr
    apply e.injective
    have hqA := (Subgroup.centerCongr e ⟨q,hq⟩).property
    exact (mem_bot.mp (hz ▸ hqA)).trans e.map_one.symm
  exact ha ((image_model E h hf hne hstar hcent hff).of_mulEquiv
    (e.symm.trans (componentQuotientImageEquiv E h hzQ)))

/-- Exclude M23 on the original two-core quotient, through its actual action map. -/
theorem not_m23_quotient
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E)) :
    ¬ Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* Sporadic.Mathieu.M23) := by
  rintro ⟨e⟩
  exact false_of_centerless_quotient_model E h hf hne hstar hcent hff e
    Sporadic.Mathieu.M23Geometry.m23_center_eq_bot not_image_model_m23

/-- Exclude J4 on the original two-core quotient, retaining the literal kernel. -/
theorem not_j4_quotient
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E)) :
    ¬ Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  exact false_of_centerless_quotient_model E h hf hne hstar hcent hff e
    Janko4.model_center_eq_bot not_image_model_j4


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
