module

public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.LinearCombination

/-!
# The intrinsic flag of the unitary norm-plane root action

The common fixed vectors give the final fixed-field coordinate. Their inverse
image in the fixed-vector quotient gives the final two coordinates. Conjugation
therefore induces three additive diagonal blocks. The root equations recover
fixed-field multiplication, the polar norm pairing and the quadratic norm term.
These are the intrinsic normalizer constraints used in the Sylow automorphism
argument of Aschbacher--Smith, F.1.11 and F.1.12.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer

variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- Conjugation by the additive normalizer, in the faithful root parameter. -/
def parameterAction : rootNormalizer F σ hσ →* MulAut (Multiplicative F) :=
  (MulAut.congr (MonoidHom.ofInjective (rootAction_injective F σ hσ)).symm).toMonoidHom.comp
    (rootAction F σ hσ).range.normalizerMonoidHom

def normalizerEquiv (g : rootNormalizer F σ hσ) : Space F σ ≃+ Space F σ :=
  AddEquiv.toMultiplicative.symm g.val

def parameterEquiv (g : rootNormalizer F σ hσ) : F ≃+ F :=
  AddEquiv.toMultiplicative.symm (parameterAction F σ hσ g)

theorem intertwine (g : rootNormalizer F σ hσ) (y : F) (v : Space F σ) :
    normalizerEquiv F σ hσ g (rootMap F σ hσ y v) =
      rootMap F σ hσ (parameterEquiv F σ hσ g y) (normalizerEquiv F σ hσ g v) := by
  have he : rootAction F σ hσ (parameterAction F σ hσ g (Multiplicative.ofAdd y)) =
      g.val * rootAction F σ hσ (Multiplicative.ofAdd y) * g.val⁻¹ := by
    let e := MonoidHom.ofInjective (rootAction_injective F σ hσ)
    exact congrArg Subtype.val (e.apply_symm_apply
      ((rootAction F σ hσ).range.normalizerMonoidHom g (e (Multiplicative.ofAdd y))))
  have hh := congrArg (fun a : MulAut (Multiplicative (Space F σ)) =>
    a (g.val (Multiplicative.ofAdd v))) he
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at hh
  exact congrArg Multiplicative.toAdd hh.symm

include hσ in
theorem pairing_nondegenerate (hnt : ∃ u, σ u ≠ u) (x : F)
    (h : ∀ y, pairing F σ hσ x y = 0) : x = 0 := by
  have h' (y : F) : σ x * y + σ y * x = 0 := by
    simpa using congrArg Subtype.val (h y)
  have hx : σ x = x := by
    have hh := h' 1
    simpa only [map_one, mul_one, one_mul, CharTwo.add_eq_zero] using hh
  obtain ⟨u, hu⟩ := hnt
  by_contra hx0
  apply hu
  apply mul_right_cancel₀ hx0
  have hh := h' u
  rw [hx, mul_comm x u] at hh
  exact (CharTwo.add_eq_zero.mp hh).symm

/-- The common fixed vectors are exactly the last fixed-field coordinate. -/
theorem fixed_iff (hnt : ∃ u, σ u ≠ u) (v : Space F σ) :
    (∀ y, rootMap F σ hσ y v = v) ↔ v.1 = 0 ∧ v.2.1 = 0 := by
  rcases v with ⟨t,x,z⟩
  constructor
  · intro h
    have ht : t = 0 := by
      apply Subtype.ext
      have hh := congrArg (fun v : Space F σ => v.2.1) (h 1)
      simpa only [rootMap_apply, mul_one, add_eq_left, Subfield.coe_zero] using hh
    refine ⟨ht, pairing_nondegenerate F σ hσ hnt x fun y => ?_⟩
    have hh := congrArg (fun v : Space F σ => v.2.2) (h y)
    simpa only [rootMap_apply, ht, zero_mul, add_zero, add_eq_left] using hh
  · rintro ⟨rfl,rfl⟩ y
    simp

/-- Every normalizing additive automorphism preserves the central coordinate. -/
theorem normalizer_central (hnt : ∃ u, σ u ≠ u)
    (g : rootNormalizer F σ hσ) (z : FixedField F σ) :
    (normalizerEquiv F σ hσ g (0,0,z)).1 = 0 ∧
      (normalizerEquiv F σ hσ g (0,0,z)).2.1 = 0 := by
  apply (fixed_iff F σ hσ hnt _).mp
  intro y
  obtain ⟨x,rfl⟩ := (parameterEquiv F σ hσ g).surjective y
  rw [← intertwine]
  simp

theorem normalizer_central_apply (hnt : ∃ u, σ u ≠ u)
    (g : rootNormalizer F σ hσ) (z : FixedField F σ) :
    normalizerEquiv F σ hσ g (0,0,z) =
      (0,0,(normalizerEquiv F σ hσ g (0,0,z)).2.2) := by
  obtain ⟨h1,h2⟩ := normalizer_central F σ hσ hnt g z
  exact Prod.ext h1 (Prod.ext h2 rfl)

/-- The inverse image of the fixed vectors in the fixed-vector quotient is the
last two coordinates, and is therefore invariant under the normalizer. -/
theorem normalizer_middle (hnt : ∃ u, σ u ≠ u)
    (g : rootNormalizer F σ hσ) (x : F) (z : FixedField F σ) :
    (normalizerEquiv F σ hσ g (0,x,z)).1 = 0 := by
  obtain ⟨y,hy⟩ := (parameterEquiv F σ hσ g).surjective 1
  have hv : rootMap F σ hσ y (0,x,z) = (0,x,z) + (0,0,pairing F σ hσ x y) := by
    simp
  have hh := congrArg (fun v : Space F σ => v.2.1) (intertwine F σ hσ g y (0,x,z))
  rw [hv, map_add, hy] at hh
  simp only [Prod.snd_add, Prod.fst_add, (normalizer_central F σ hσ hnt g _).2,
    add_zero] at hh
  change _ = _ + _ * 1 at hh
  apply Subtype.ext
  simpa only [mul_one, left_eq_add, Subfield.coe_zero] using hh

/-- The diagonal block on the first fixed-field coordinate. -/
def topMap (g : rootNormalizer F σ hσ) : FixedField F σ →+ FixedField F σ where
  toFun t := (normalizerEquiv F σ hσ g (t,0,0)).1
  map_zero' := by
    exact congrArg (fun v : Space F σ => v.1) (normalizerEquiv F σ hσ g).map_zero
  map_add' t u := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.fst_add] using congrArg (fun v : Space F σ => v.1)
      ((normalizerEquiv F σ hσ g).map_add (t,0,0) (u,0,0))

/-- The diagonal block on the middle extension-field coordinate. -/
def middleMap (g : rootNormalizer F σ hσ) : F →+ F where
  toFun x := (normalizerEquiv F σ hσ g (0,x,0)).2.1
  map_zero' := by
    exact congrArg (fun v : Space F σ => v.2.1) (normalizerEquiv F σ hσ g).map_zero
  map_add' x y := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add, Prod.fst_add] using congrArg (fun v : Space F σ => v.2.1)
      ((normalizerEquiv F σ hσ g).map_add (0,x,0) (0,y,0))

/-- The diagonal block on the final fixed-field coordinate. -/
def centralMap (g : rootNormalizer F σ hσ) : FixedField F σ →+ FixedField F σ where
  toFun z := (normalizerEquiv F σ hσ g (0,0,z)).2.2
  map_zero' := by
    exact congrArg (fun v : Space F σ => v.2.2) (normalizerEquiv F σ hσ g).map_zero
  map_add' z w := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add] using congrArg (fun v : Space F σ => v.2.2)
      ((normalizerEquiv F σ hσ g).map_add (0,0,z) (0,0,w))

@[simp] theorem topMap_apply (g : rootNormalizer F σ hσ) (t : FixedField F σ) :
    topMap F σ hσ g t = (normalizerEquiv F σ hσ g (t,0,0)).1 := rfl

@[simp] theorem middleMap_apply (g : rootNormalizer F σ hσ) (x : F) :
    middleMap F σ hσ g x = (normalizerEquiv F σ hσ g (0,x,0)).2.1 := rfl

@[simp] theorem centralMap_apply (g : rootNormalizer F σ hσ) (z : FixedField F σ) :
    centralMap F σ hσ g z = (normalizerEquiv F σ hσ g (0,0,z)).2.2 := rfl

theorem normalizer_top (hnt : ∃ u, σ u ≠ u)
    (g : rootNormalizer F σ hσ) (v : Space F σ) :
    (normalizerEquiv F σ hσ g v).1 = topMap F σ hσ g v.1 := by
  rcases v with ⟨t,x,z⟩
  have h : (t,x,z) = (t,0,0) + (0,x,z) := by simp
  change _ = (normalizerEquiv F σ hσ g (t,0,0)).1
  rw [h, map_add]
  simp only [Prod.fst_add, normalizer_middle F σ hσ hnt, add_zero]

theorem normalizer_middle_coordinate (hnt : ∃ u, σ u ≠ u)
    (g : rootNormalizer F σ hσ) (v : Space F σ) :
    (normalizerEquiv F σ hσ g v).2.1 =
      (normalizerEquiv F σ hσ g (v.1,0,0)).2.1 + middleMap F σ hσ g v.2.1 := by
  rcases v with ⟨t,x,z⟩
  have h : (t,x,z) = (t,0,0) + ((0,x,0) + (0,0,z)) := by simp
  change _ = (normalizerEquiv F σ hσ g (t,0,0)).2.1 +
    (normalizerEquiv F σ hσ g (0,x,0)).2.1
  rw [h, map_add, map_add]
  simp only [Prod.snd_add, Prod.fst_add, (normalizer_central F σ hσ hnt g z).2, add_zero]

@[simp] theorem normalizerEquiv_inv (g : rootNormalizer F σ hσ) :
    normalizerEquiv F σ hσ g⁻¹ = (normalizerEquiv F σ hσ g).symm := rfl

@[simp] theorem normalizerEquiv_mul (g h : rootNormalizer F σ hσ) (v : Space F σ) :
    normalizerEquiv F σ hσ (g*h) v =
      normalizerEquiv F σ hσ g (normalizerEquiv F σ hσ h v) := rfl

theorem topMap_injective (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    Function.Injective (topMap F σ hσ g) := by
  have hi (t : FixedField F σ) : topMap F σ hσ g⁻¹ (topMap F σ hσ g t) = t := by
    have hh := normalizer_top F σ hσ hnt g⁻¹ (normalizerEquiv F σ hσ g (t,0,0))
    simpa only [topMap_apply, normalizerEquiv_inv, AddEquiv.symm_apply_apply] using hh.symm
  exact Function.LeftInverse.injective hi

theorem topMap_surjective (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    Function.Surjective (topMap F σ hσ g) := by
  intro t
  refine ⟨topMap F σ hσ g⁻¹ t, ?_⟩
  have hh := normalizer_top F σ hσ hnt g (normalizerEquiv F σ hσ g⁻¹ (t,0,0))
  simpa only [topMap_apply, normalizerEquiv_inv, AddEquiv.apply_symm_apply] using hh.symm

theorem centralMap_injective (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    Function.Injective (centralMap F σ hσ g) := by
  intro z w h
  have hh : normalizerEquiv F σ hσ g (0,0,z) = normalizerEquiv F σ hσ g (0,0,w) := by
    rw [normalizer_central_apply F σ hσ hnt g z, normalizer_central_apply F σ hσ hnt g w]
    exact congrArg (fun u : FixedField F σ => (0,0,u)) h
  exact congrArg (fun v : Space F σ => v.2.2) ((normalizerEquiv F σ hσ g).injective hh)

/-- The first off-diagonal block recovers multiplication by the fixed field. -/
theorem middleMap_fixed_mul (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (y : F) :
    middleMap F σ hσ g ((t:F)*y) = (topMap F σ hσ g t : F) * parameterEquiv F σ hσ g y := by
  have hh := congrArg (fun v : Space F σ => v.2.1) (intertwine F σ hσ g y (t,0,0))
  rw [normalizer_middle_coordinate F σ hσ hnt] at hh
  simp only [rootMap_apply, zero_add, pairing_zero_left, add_zero] at hh
  change _ + middleMap F σ hσ g ((t:F)*y) =
    _ + (topMap F σ hσ g t : F) * parameterEquiv F σ hσ g y at hh
  exact add_left_cancel hh

/-- The second off-diagonal block recovers the polar norm form. -/
theorem centralMap_pairing (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ)
    (x y : F) :
    centralMap F σ hσ g (pairing F σ hσ x y) =
      pairing F σ hσ (middleMap F σ hσ g x) (parameterEquiv F σ hσ g y) := by
  have hv : rootMap F σ hσ y (0,x,0) = (0,x,0) + (0,0,pairing F σ hσ x y) := by simp
  have hh := congrArg (fun v : Space F σ => v.2.2) (intertwine F σ hσ g y (0,x,0))
  rw [hv, map_add] at hh
  change _ + centralMap F σ hσ g _ = _ + _ + _ at hh
  rw [normalizer_middle F σ hσ hnt, zero_mul, add_zero] at hh
  exact add_left_cancel hh

theorem topMap_one_ne_zero (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) :
    topMap F σ hσ g 1 ≠ 0 := by
  intro h
  apply (one_ne_zero : (1 : FixedField F σ) ≠ 0)
  exact topMap_injective F σ hσ hnt g (h.trans (map_zero _).symm)

theorem parameterEquiv_one_ne_zero (g : rootNormalizer F σ hσ) :
    parameterEquiv F σ hσ g 1 ≠ 0 := by simp

theorem middleMap_eq (hnt : ∃ u, σ u ≠ u) (g : rootNormalizer F σ hσ) (y : F) :
    middleMap F σ hσ g y = (topMap F σ hσ g 1 : F) * parameterEquiv F σ hσ g y := by
  simpa using middleMap_fixed_mul F σ hσ hnt g 1 y

/-- The norm pairing takes every fixed-field value, already on the line `x=1`. -/
theorem pairing_one_surjective (hnt : ∃ u, σ u ≠ u) :
    Function.Surjective (pairing F σ hσ 1) := by
  obtain ⟨u,hu⟩ := hnt
  have hp : pairing F σ hσ 1 u ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val h
    simp only [pairing_val, map_one, one_mul, mul_one, Subfield.coe_zero,
      CharTwo.add_eq_zero] at hh
    exact hu hh.symm
  intro t
  refine ⟨((t / pairing F σ hσ 1 u : FixedField F σ) : F) * u, ?_⟩
  rw [pairing_fixed_mul_right, div_mul_cancel₀ _ hp]

/-- The final coordinate decomposes into its three additive blocks. -/
theorem normalizer_last_coordinate (g : rootNormalizer F σ hσ) (v : Space F σ) :
    (normalizerEquiv F σ hσ g v).2.2 =
      (normalizerEquiv F σ hσ g (v.1,0,0)).2.2 +
      (normalizerEquiv F σ hσ g (0,v.2.1,0)).2.2 + centralMap F σ hσ g v.2.2 := by
  rcases v with ⟨t,x,z⟩
  have hv : (t,x,z) = (t,0,0) + (0,x,0) + (0,0,z) := by simp
  conv_lhs => rw [hv]
  rw [map_add, map_add]
  rfl

/-- The nonlinear root-coordinate equation retained by an additive normalizer. -/
theorem normalizer_norm_equation (g : rootNormalizer F σ hσ)
    (t : FixedField F σ) (y : F) :
    (normalizerEquiv F σ hσ g (0,(t:F)*y,0)).2.2 +
      centralMap F σ hσ g (t * norm F σ hσ y) =
      pairing F σ hσ (normalizerEquiv F σ hσ g (t,0,0)).2.1
        (parameterEquiv F σ hσ g y) +
      topMap F σ hσ g t * norm F σ hσ (parameterEquiv F σ hσ g y) := by
  have hh := congrArg (fun v : Space F σ => v.2.2) (intertwine F σ hσ g y (t,0,0))
  rw [normalizer_last_coordinate] at hh
  simp only [rootMap_apply, zero_add, pairing_zero_left, add_zero] at hh
  change _ + _ + _ = _ + _ + _ at hh
  exact add_left_cancel (by simpa only [add_assoc, topMap_apply] using hh)

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
