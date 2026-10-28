module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Additivity

/-!
# Additivity and scalar invariance for the short–short correction

The two upper trace relations supply the polar terms when either short
parameter is added. Thus the polynomial conjugation candidates are additive
in the covering group. A central difference of additive maps is additive;
a biadditive pairing invariant under simultaneous nonzero field scalars
vanishes when the characteristic-two field has more than four elements.

The scalar argument adapts the internal proof in
`Theory.GroupTheory.Commutator.ScalarInvariantRoot`, without changing that
shared module. Source: GLS3 §2.4.5(b)(4) and §6.1; Aschbacher–Smith I.1.3.
-/

set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization.ShortPair
open RootSections RootSections.ShortPolynomial
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn
local notation "K" => ExtensionField P
local notation "F" => fieldFrobenius P
local notation "T" => cubicTrace P

/-- The complete correction, retaining both shifted trace terms. -/
def correction (L : RootSections n hn f) (s t : K) : E :=
  L.shortValue 2 (higherCoefficient P s t) * L.longValue 1 (T (s*F s*F (F t))) *
    L.longValue 2 (T (s*F t*F (F t)))

theorem correction_inv (L : RootSections n hn f) (hC : L.CommutingRelations)
    (s t : K) : (correction L s t)⁻¹ = correction L s t := by
  simp only [correction, mul_inv_rev, short_inv, long_inv]
  rw [(hC.short2_long1 _ _).symm.eq, (hC.short2_long2 _ _).symm.left_comm,
    (hC.long1_long2 _ _).symm.eq]
  exact (mul_assoc _ _ _).symm

theorem candidate_left_add (L : RootSections n hn f) (hC : L.CommutingRelations)
    (h02 : ∀ s t, L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s * L.longValue 1 (T (F (F s)*t)))
    (t s u : K) :
    L.shortValue 0 (s+u) * correction L (s+u) t =
      (L.shortValue 0 s * correction L s t) *
        (L.shortValue 0 u * correction L u t) := by
  simpa only [correction, mul_assoc] using candidate01_add L hC h02 t s u

theorem candidate_right_add (L : RootSections n hn f) (hC : L.CommutingRelations)
    (h12 : ∀ s t, L.shortValue 1 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 1 s * L.longValue 2 (T (F (F s)*t)))
    (s t u : K) :
    L.shortValue 1 (t+u) * correction L s (t+u) =
      (L.shortValue 1 t * correction L s t) *
        (L.shortValue 1 u * correction L s u) := by
  simp only [correction, mul_assoc, append_relation (hC.short1_long1 _ _).symm.eq,
    append_relation (hC.short1_long2 _ _).symm.eq,
    append_relation (hC.short2_long1 _ _).symm.eq,
    append_relation (hC.short2_long2 _ _).symm.eq,
    append_relation (hC.long1_long2 _ _).symm.eq,
    append_relation (reverse_trace L 1 2 h12 _ _), join_short, join_long, ← ShortPolynomial.long_add]
  repeat' first
    | apply congrArg₂ (fun a b : E => a*b)
    | apply congrArg (L.shortValue _)
    | apply congrArg (L.longValue _)
  all_goals first
    | rfl
    | (apply Subtype.ext
       simp only [higherCoefficient, cubicTrace_coe, Subfield.coe_add, map_add, map_mul,
         fieldFrobenius_three]
       ring)
    | (simp only [higherCoefficient, map_add, map_mul]; ring)

/-- Central differences of two additive maps are additive. -/
theorem difference_add {A : Type*} [Add A] (a b : A → E)
    (ha : ∀ x y, a (x+y) = a x*a y) (hb : ∀ x y, b (x+y) = b x*b y)
    (hd : ∀ x, (a x)⁻¹*b x ∈ Subgroup.center E) (x y : A) :
    (a (x+y))⁻¹*b (x+y) = ((a x)⁻¹*b x)*((a y)⁻¹*b y) := by
  rw [ha, hb, mul_inv_rev]
  calc
    _ = (a y)⁻¹*((a x)⁻¹*b x)*b y := by group
    _ = ((a x)⁻¹*b x)*(a y)⁻¹*b y := by
      rw [Subgroup.mem_center_iff.mp (hd x) ((a y)⁻¹)]
    _ = _ := by group

/-- A simultaneous-scalar invariant biadditive pairing vanishes over GF(8).
The elementary argument is adapted from `Commutator.ScalarInvariantRoot`. -/
theorem invariant_pairing_eq_one {Fld A : Type*} [Field Fld] [Finite Fld] [CharP Fld 2]
    [Group A] (hFld : 4 < Nat.card Fld) (b : Fld → Fld → A)
    (hl : ∀ x y z, b (x + y) z = b x z * b y z)
    (hr : ∀ x y z, b x (y + z) = b x y * b x z)
    (hi : ∀ c : Fld, c ≠ 0 → ∀ x y, b (c * x) (c * y) = b x y)
    (x y : Fld) : b x y = 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fldˣ)
  have ha3 : ¬ a ^ 3 = 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha, Nat.card_units] at hd
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  have hc1 : 1 + (a : Fld) ≠ 0 := by
    intro h
    have he : (a : Fld) = 1 := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h
    apply ha3
    apply Units.ext
    simp [he]
  have hne : (1 + (a : Fld))⁻¹ ≠ 1 + (a : Fld)⁻¹ := by
    intro h
    apply ha3
    have he : (a : Fld)^2 + a + 1 = 0 := by
      field_simp at h
      linear_combination -h
    apply Units.ext
    change (a : Fld)^3 = 1
    linear_combination ((a : Fld)-1)*he
  have hz (v : Fld) : b v 0 = 1 := by
    have h := hr v 0 0
    apply mul_left_cancel (a := b v 0)
    simpa only [add_zero, mul_one] using h.symm
  have hn (v z : Fld) : b v (-z) = (b v z)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hr, add_neg_cancel, hz]
  have hs (s : Fld) (h : s ≠ 0) (v w : Fld) : b (s * v) w = b v (s⁻¹ * w) := by
    simpa only [mul_inv_cancel_left₀ h] using hi s h v (s⁻¹ * w)
  have he (w : Fld) : b x ((1 + (a : Fld))⁻¹ * w) = b x ((1 + (a : Fld)⁻¹) * w) := by
    rw [← hs (1 + (a : Fld)) hc1, add_mul, one_mul, hl, hs a a.ne_zero,
      add_mul, one_mul, hr]
  let d : Fld := (1 + (a : Fld))⁻¹ - (1 + (a : Fld)⁻¹)
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hy : y = (1 + (a : Fld))⁻¹*(y / d) + -((1 + (a : Fld)⁻¹) * (y / d)) := by
    calc
      y = d * (y / d) := by field_simp
      _ = _ := by dsimp [d]; ring
  rw [hy, hr, hn, he, mul_inv_cancel]
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization.ShortPair
