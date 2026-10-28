module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Central lifts of a root group with its full scalar action

Let the additive group of a finite characteristic-two field of order greater
than four map into a quotient group. If every nonzero field scalar acts on
this image by conjugation, its full preimage in any central extension is
abelian. Commutators of lifts give a biadditive pairing fixed by simultaneous
scalar multiplication. Moving a scalar between the two arguments replaces
it by its inverse; additivity then compares `(1 + c)⁻¹` with `1 + c⁻¹`.
A generator of the field's unit group makes these unequal, forcing the pairing
to vanish. No field-bilinearity is assumed.

This supplies the defining-characteristic step for the even PSL₂ multiplier
calculation in Aschbacher–Smith I.1.3–I.1.4 and GLS III, Section 6.1.
-/

namespace CentralExtension

private theorem exists_scalar (F : Type*) [Field F] [Finite F] [CharP F 2] (hF : 4 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ 1 + c ≠ 0 ∧ (1 + c)⁻¹ ≠ 1 + c⁻¹ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have ha3 : ¬ a ^ 3 = 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha, Nat.card_units] at hd
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  refine ⟨a, a.ne_zero, ?_, ?_⟩
  · intro h
    apply ha3
    have he : (a : F) = 1 := by
      have : (a : F) = -1 := eq_neg_of_add_eq_zero_right h
      simpa only [CharTwo.neg_eq] using this
    apply Units.ext
    simp [he]
  · intro h
    apply ha3
    have hc : 1 + (a : F) ≠ 0 := by
      intro hz
      have : (a : F) = 1 := by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hz
      apply ha3
      apply Units.ext
      simp [this]
    have he : (a : F) ^ 2 + a + 1 = 0 := by
      field_simp at h
      linear_combination -h
    apply Units.ext
    change (a : F) ^ 3 = 1
    linear_combination ((a : F) - 1) * he

open scoped commutatorElement

private theorem invariant_pairing_eq_one {F A : Type*} [Field F] [Group A]
    (b : F → F → A)
    (hl : ∀ x y z, b (x + y) z = b x z * b y z)
    (hr : ∀ x y z, b x (y + z) = b x y * b x z)
    (hi : ∀ c : F, c ≠ 0 → ∀ x y, b (c * x) (c * y) = b x y)
    (c : F) (hc : c ≠ 0) (hc1 : 1 + c ≠ 0)
    (hne : (1 + c)⁻¹ ≠ 1 + c⁻¹) (x y : F) : b x y = 1 := by
  have hz (v : F) : b v 0 = 1 := by
    have h := hr v 0 0
    apply mul_left_cancel (a := b v 0)
    simpa only [add_zero, mul_one] using h.symm
  have hn (v z : F) : b v (-z) = (b v z)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hr, add_neg_cancel, hz]
  have hs (s : F) (h : s ≠ 0) (v w : F) : b (s * v) w = b v (s⁻¹ * w) := by
    simpa only [mul_inv_cancel_left₀ h] using hi s h v (s⁻¹ * w)
  have he (w : F) : b x ((1 + c)⁻¹ * w) = b x ((1 + c⁻¹) * w) := by
    rw [← hs (1 + c) hc1, add_mul, one_mul, hl, hs c hc, add_mul, one_mul, hr]
  let d : F := (1 + c)⁻¹ - (1 + c⁻¹)
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hy : y = (1 + c)⁻¹*(y / d) + -((1 + c⁻¹) * (y / d)) := by
    calc
      y = d * (y / d) := by field_simp
      _ = _ := by dsimp [d]; ring
  rw [hy, hr, hn, he, mul_inv_cancel]

private theorem commutator_same_fiber {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E)
    {x x' y y' : E} (hx : f x = f x') (hy : f y = f y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hleft {a a' z : E} (h : f a = f a') : ⁅a, z⁆ = ⁅a', z⁆ := by
    have hk' : a * a'⁻¹ ∈ Subgroup.center E := hk (by simp [MonoidHom.mem_ker, h])
    have hcomm (t : E) : Commute (a * a'⁻¹) t :=
      (Subgroup.mem_center_iff.mp hk' t).symm
    calc
      ⁅a, z⁆ = ⁅(a * a'⁻¹)* a', z⁆ := by simp
      _ = ⁅a', z⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, (hcomm z).commutator_eq,
          (hcomm ⁅a', z⁆).eq]
        simp [mul_assoc]
  rw [hleft hx, ← commutatorElement_inv y x', hleft hy, commutatorElement_inv]

private theorem lift_pairing {F E B : Type*} [Field F] [Group E] [Group B]
    (f : E →* B) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative F →* B)
    (hscale : ∀ c : F, c ≠ 0 → ∃ t : B,
      ∀ x : F, t * u (.ofAdd x) * t⁻¹ = u (.ofAdd (c * x))) :
    ∃ b : F → F → E,
      (∀ x y z, b (x + y) z = b x z * b y z) ∧
      (∀ x y z, b x (y + z) = b x y * b x z) ∧
      (∀ c : F, c ≠ 0 → ∀ x y, b (c * x) (c * y) = b x y) ∧
      (∀ x y v w, f v = u (.ofAdd x) → f w = u (.ofAdd y) → b x y = ⁅v, w⁆) := by
  choose s hs using fun x : F => hf (u (.ofAdd x))
  let b : F → F → E := fun x y => ⁅s x, s y⁆
  have hb (x y : F) : b x y ∈ Subgroup.center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement, hs, hs]
    exact ((Commute.all (.ofAdd x) (.ofAdd y)).map u).commutator_eq
  have he (x y : F) (v w : E) (hv : f v = u (.ofAdd x))
      (hw : f w = u (.ofAdd y)) : b x y = ⁅v, w⁆ :=
    commutator_same_fiber f hk ((hs x).trans hv.symm) ((hs y).trans hw.symm)
  refine ⟨b, ?_, ?_, ?_, he⟩
  · intro x y z
    rw [he (x + y) z (s y * s x) (s z) (by
      rw [map_mul, hs, hs, ← map_mul]; congr 1; exact add_comm y x) (hs z),
      commutatorElement_mul_left_eq_conj_mul]
    change s y * b x z * (s y)⁻¹ * b y z = _
    rw [Subgroup.mem_center_iff.mp (hb x z) (s y)]
    simp [mul_assoc]
  · intro x y z
    rw [he x (y + z) (s x) (s y * s z) (hs x) (by rw [map_mul, hs, hs, ← map_mul]; rfl),
      commutatorElement_mul_right_eq_mul_conj]
    change b x y * s y * b x z * (s y)⁻¹ = _
    rw [mul_assoc (b x y), Subgroup.mem_center_iff.mp (hb x z) (s y)]
    simp [mul_assoc]
  · intro c hc x y
    obtain ⟨t, ht⟩ := hscale c hc
    obtain ⟨a, ha⟩ := hf t
    rw [he (c * x) (c * y) (a * s x * a⁻¹) (a * s y * a⁻¹)
      (by rw [map_mul, map_mul, map_inv, ha, hs, ht])
      (by rw [map_mul, map_mul, map_inv, ha, hs, ht]), ← conjugate_commutatorElement]
    change a * b x y * a⁻¹ = _
    rw [Subgroup.mem_center_iff.mp (hb x y) a]
    simp [mul_assoc]

/-- The full preimage of an additive root group is abelian when the scalar group
acts by conjugation in the quotient and the central kernel is fixed. -/
public theorem commute_lifts_of_full_scalar_action {F E B : Type*} [Field F] [Finite F] [CharP F 2]
    [Group E] [Group B] (hF : 4 < Nat.card F)
    (f : E →* B) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative F →* B)
    (hscale : ∀ c : F, c ≠ 0 → ∃ t : B,
      ∀ x : F, t * u (.ofAdd x) * t⁻¹ = u (.ofAdd (c * x)))
    {v w : E} (hv : f v ∈ u.range) (hw : f w ∈ u.range) : Commute v w := by
  obtain ⟨b, hl, hr, hi, he⟩ := lift_pairing f hf hk u hscale
  obtain ⟨c, hc, hc1, hne⟩ := exists_scalar F hF
  obtain ⟨x, hx⟩ := hv
  obtain ⟨y, hy⟩ := hw
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← he x.toAdd y.toAdd v w hx.symm hy.symm]
  exact invariant_pairing_eq_one b hl hr hi c hc hc1 hne _ _

end CentralExtension
