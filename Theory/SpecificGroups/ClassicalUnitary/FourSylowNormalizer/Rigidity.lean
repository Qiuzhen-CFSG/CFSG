module

public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Coordinates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of the unitary-four root parameter action

The first off-diagonal block reconstructs the fixed-field automorphism. The
polar form then determines the final diagonal block. Comparing the full norm
identity at a nonbinary fixed scalar twice shows that its quadratic defect is
zero: a quadratic homogeneous defect cannot also be linear in that scalar.
Thus the induced root-parameter automorphism is a semilinear norm similarity.
This supplies the field-recovery step in the unitary-four Sylow automorphism
argument, Aschbacher--Smith F.1.11 and F.1.12.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer

variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

def fixedMap (g : rootNormalizer F σ hσ) : FixedField F σ →+ FixedField F σ where
  toFun t := topMap F σ hσ g t / topMap F σ hσ g 1
  map_zero' := by simp only [map_zero, zero_div]
  map_add' t u := by simp only [map_add, add_div]

@[simp] theorem fixedMap_apply (g : rootNormalizer F σ hσ) (t : FixedField F σ) :
    fixedMap F σ hσ g t = topMap F σ hσ g t / topMap F σ hσ g 1 := rfl

theorem fixedMap_one (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    fixedMap F σ hσ g 1 = 1 := div_self (topMap_one_ne_zero F σ hσ hnt g)

theorem parameter_fixed_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (x : F) :
    parameterEquiv F σ hσ g ((t:F)*x) =
      (fixedMap F σ hσ g t : F) * parameterEquiv F σ hσ g x := by
  have ha : (topMap F σ hσ g 1 : F) ≠ 0 :=
    Subtype.coe_ne_coe.mpr (topMap_one_ne_zero F σ hσ hnt g)
  have hh := middleMap_fixed_mul F σ hσ hnt g t x
  rw [middleMap_eq F σ hσ hnt] at hh
  apply mul_left_cancel₀ ha
  rw [hh]
  rw [fixedMap_apply, Subfield.coe_div]
  field_simp

theorem fixedMap_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t u : FixedField F σ) :
    fixedMap F σ hσ g (t*u) = fixedMap F σ hσ g t * fixedMap F σ hσ g u := by
  apply Subtype.ext
  apply mul_right_cancel₀ (parameterEquiv_one_ne_zero F σ hσ g)
  have hh := parameter_fixed_mul F σ hσ hnt g (t*u) 1
  have ht := parameter_fixed_mul F σ hσ hnt g t ((u:F)*1)
  rw [parameter_fixed_mul F σ hσ hnt g u 1] at ht
  rw [← hh]
  simpa only [Subfield.coe_mul, mul_assoc] using ht

/-- The root parameter action reconstructs an automorphism of the fixed field. -/
def fixedEquiv (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    FixedField F σ ≃+* FixedField F σ :=
  RingEquiv.ofBijective
    ({ toFun := fixedMap F σ hσ g
       map_zero' := map_zero _
       map_add' := map_add _
       map_one' := fixedMap_one F σ hσ hnt g
       map_mul' := fixedMap_mul F σ hσ hnt g } : FixedField F σ →+* FixedField F σ)
    ⟨fun t u h => topMap_injective F σ hσ hnt g
      ((div_left_inj' (topMap_one_ne_zero F σ hσ hnt g)).mp h), by
      intro t
      obtain ⟨u,hu⟩ := topMap_surjective F σ hσ hnt g (t * topMap F σ hσ g 1)
      refine ⟨u, ?_⟩
      change topMap F σ hσ g u / topMap F σ hσ g 1 = t
      rw [hu, mul_div_cancel_right₀ _ (topMap_one_ne_zero F σ hσ hnt g)]⟩

@[simp] theorem fixedEquiv_apply (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) : fixedEquiv F σ hσ hnt g t = fixedMap F σ hσ g t := rfl

theorem topMap_eq (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) :
    topMap F σ hσ g t = topMap F σ hσ g 1 * fixedEquiv F σ hσ hnt g t := by
  rw [fixedEquiv_apply, fixedMap_apply, mul_div_cancel₀ _ (topMap_one_ne_zero F σ hσ hnt g)]

theorem centralMap_fixed_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t u : FixedField F σ) :
    centralMap F σ hσ g (t*u) = fixedEquiv F σ hσ hnt g t * centralMap F σ hσ g u := by
  obtain ⟨y,rfl⟩ := pairing_one_surjective F σ hσ hnt u
  rw [← pairing_fixed_mul_left, centralMap_pairing F σ hσ hnt,
    centralMap_pairing F σ hσ hnt]
  rw [middleMap_eq F σ hσ hnt, parameter_fixed_mul F σ hσ hnt,
    middleMap_eq F σ hσ hnt]
  rw [← mul_assoc, mul_comm (topMap F σ hσ g 1 : F), mul_assoc,
    pairing_fixed_mul_left]
  rfl

theorem centralMap_eq (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) :
    centralMap F σ hσ g t = centralMap F σ hσ g 1 * fixedEquiv F σ hσ hnt g t := by
  simpa [mul_comm] using centralMap_fixed_mul F σ hσ hnt g t 1

omit [CharP F 2] in
theorem norm_fixed_mul (t : FixedField F σ) (x : F) :
    norm F σ hσ ((t:F)*x) = t^2 * norm F σ hσ x := by
  have ht : σ (t:F) = t := t.property
  apply Subtype.ext
  simp only [norm_val, map_mul, ht, Subfield.coe_mul, SubmonoidClass.coe_pow]
  ring

theorem parameter_fixedEquiv_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (x : F) :
    parameterEquiv F σ hσ g ((t:F)*x) =
      (fixedEquiv F σ hσ hnt g t : F) * parameterEquiv F σ hσ g x :=
  parameter_fixed_mul F σ hσ hnt g t x

def normDefect (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) (y : F) : FixedField F σ :=
  topMap F σ hσ g 1 * norm F σ hσ (parameterEquiv F σ hσ g y) -
    centralMap F σ hσ g 1 * fixedEquiv F σ hσ hnt g (norm F σ hσ y)

theorem normDefect_fixed_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (y : F) :
    normDefect F σ hσ hnt g ((t:F)*y) =
      (fixedEquiv F σ hσ hnt g t)^2 * normDefect F σ hσ hnt g y := by
  simp only [normDefect, parameter_fixedEquiv_mul F σ hσ hnt, norm_fixed_mul,
    map_mul, map_pow]
  ring

theorem lowerShift_eq (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) (y : F) :
    (normalizerEquiv F σ hσ g (0,y,0)).2.2 =
      pairing F σ hσ (normalizerEquiv F σ hσ g (1,0,0)).2.1
        (parameterEquiv F σ hσ g y) + normDefect F σ hσ hnt g y := by
  have hh := normalizer_norm_equation F σ hσ g 1 y
  simp only [Subfield.coe_one, one_mul] at hh
  rw [centralMap_eq F σ hσ hnt] at hh
  dsimp only [normDefect]
  linear_combination hh

theorem normDefect_relation (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (y : F) :
    ((fixedEquiv F σ hσ hnt g t)^2 - fixedEquiv F σ hσ hnt g t) * normDefect F σ hσ hnt g y =
      pairing F σ hσ (normalizerEquiv F σ hσ g (t,0,0)).2.1 (parameterEquiv F σ hσ g y) -
      fixedEquiv F σ hσ hnt g t *
        pairing F σ hσ (normalizerEquiv F σ hσ g (1,0,0)).2.1 (parameterEquiv F σ hσ g y) := by
  have hh := normalizer_norm_equation F σ hσ g t y
  rw [lowerShift_eq F σ hσ hnt, normDefect_fixed_mul, parameter_fixedEquiv_mul F σ hσ hnt,
    pairing_fixed_mul_right, centralMap_eq F σ hσ hnt, map_mul, topMap_eq F σ hσ hnt] at hh
  dsimp only [normDefect] at hh ⊢
  linear_combination hh

/-- A nonbinary fixed field prevents a quadratic norm defect from being hidden
inside an additive central-coordinate shear. -/
theorem normDefect_zero (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (y : F) :
    normDefect F σ hσ hnt g y = 0 := by
  let b := fixedEquiv F σ hσ hnt g t
  have hb0 : b ≠ 0 := map_ne_zero _ |>.mpr ht0
  have hb1 : b ≠ 1 := by
    intro h
    exact ht1 ((fixedEquiv F σ hσ hnt g).injective (h.trans (map_one _).symm))
  have hd : b^2-b ≠ 0 := by
    rw [show b^2-b = b*(b-1) by ring]
    exact mul_ne_zero hb0 (sub_ne_zero.mpr hb1)
  have h1 := normDefect_relation F σ hσ hnt g t y
  have h2 := normDefect_relation F σ hσ hnt g t ((t:F)*y)
  rw [normDefect_fixed_mul, parameter_fixedEquiv_mul F σ hσ hnt,
    pairing_fixed_mul_right, pairing_fixed_mul_right] at h2
  have hz : (b^2-b)^2 * normDefect F σ hσ hnt g y = 0 := by
    dsimp only [b]
    linear_combination h2 - fixedEquiv F σ hσ hnt g t * h1
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hd)

/-- The root parameter action is a semilinear similarity of the quadratic norm. -/
theorem parameter_norm (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (y : F) :
    norm F σ hσ (parameterEquiv F σ hσ g y) =
      norm F σ hσ (parameterEquiv F σ hσ g 1) *
        fixedEquiv F σ hσ hnt g (norm F σ hσ y) := by
  have hy := normDefect_zero F σ hσ hnt g t ht0 ht1 y
  have h1 := normDefect_zero F σ hσ hnt g t ht0 ht1 1
  change _ - _ = 0 at hy h1
  rw [sub_eq_zero] at hy h1
  simp only [norm_one, map_one, mul_one] at h1
  rw [← h1] at hy
  apply mul_left_cancel₀ (topMap_one_ne_zero F σ hσ hnt g)
  simpa only [mul_assoc] using hy

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
