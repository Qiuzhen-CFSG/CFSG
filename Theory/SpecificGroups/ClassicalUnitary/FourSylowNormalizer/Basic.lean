module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-!
# The norm-plane root action in a unitary-four Sylow group

The additive coordinates are `K × F × K`, where `K` is the fixed field of an
involutive field automorphism. The root parameter `y` acts by
`(t,x,z) ↦ (t,x+t*y,z+Tr(σ(x)*y)+t*N(y))`. This is the abelian normal
subgroup action used to study automorphisms of the unitary-four Sylow group
in Aschbacher--Smith, F.1.11 and F.1.12.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer

variable (F : Type*) [Field F] (σ : F ≃+* F)

abbrev FixedField := FixedBy.subfield F σ
abbrev Space := FixedField F σ × F × FixedField F σ

variable (hσ : Function.Involutive σ)

/-- The field trace with its value in the fixed subfield. -/
def trace (x : F) : FixedField F σ :=
  ⟨x + σ x, by change σ (x + σ x) = x + σ x; rw [map_add, hσ x, add_comm]⟩

/-- The quadratic norm with its value in the fixed subfield. -/
def norm (x : F) : FixedField F σ :=
  ⟨σ x * x, by change σ (σ x * x) = σ x * x; rw [map_mul, hσ x, mul_comm]⟩

/-- The polar form of the quadratic norm. -/
def pairing (x y : F) : FixedField F σ := trace F σ hσ (σ x * y)

@[simp] theorem trace_val (x : F) : (trace F σ hσ x : F) = x + σ x := rfl
@[simp] theorem norm_val (x : F) : (norm F σ hσ x : F) = σ x * x := rfl
@[simp] theorem pairing_val (x y : F) :
    (pairing F σ hσ x y : F) = σ x * y + σ y * x := by
  simp [pairing, map_mul, hσ x, mul_comm]

@[simp] theorem trace_add (x y : F) :
    trace F σ hσ (x+y) = trace F σ hσ x + trace F σ hσ y := by
  apply Subtype.ext
  simp [map_add, add_comm, add_left_comm, add_assoc]

@[simp] theorem norm_zero : norm F σ hσ 0 = 0 := by ext; simp
@[simp] theorem norm_one : norm F σ hσ 1 = 1 := by ext; simp
@[simp] theorem pairing_zero_left (y : F) : pairing F σ hσ 0 y = 0 := by ext; simp
@[simp] theorem pairing_zero_right (x : F) : pairing F σ hσ x 0 = 0 := by ext; simp

@[simp] theorem pairing_add_left (x y z : F) :
    pairing F σ hσ (x+y) z = pairing F σ hσ x z + pairing F σ hσ y z := by
  apply Subtype.ext
  simp only [pairing_val, Subfield.coe_add, map_add]
  ring

@[simp] theorem pairing_add_right (x y z : F) :
    pairing F σ hσ x (y+z) = pairing F σ hσ x y + pairing F σ hσ x z := by
  apply Subtype.ext
  simp only [pairing_val, Subfield.coe_add, map_add]
  ring

theorem pairing_comm (x y : F) : pairing F σ hσ x y = pairing F σ hσ y x := by
  apply Subtype.ext
  simp only [pairing_val, add_comm]

@[simp] theorem pairing_fixed_mul_left (t : FixedField F σ) (x y : F) :
    pairing F σ hσ ((t : F)*x) y = t * pairing F σ hσ x y := by
  have ht : σ (t : F) = t := t.property
  apply Subtype.ext
  simp only [pairing_val, map_mul, ht, Subfield.coe_mul]
  ring

@[simp] theorem pairing_fixed_mul_right (t : FixedField F σ) (x y : F) :
    pairing F σ hσ x ((t : F)*y) = t * pairing F σ hσ x y := by
  rw [pairing_comm, pairing_fixed_mul_left, pairing_comm F σ hσ y x]

theorem norm_add (x y : F) : norm F σ hσ (x+y) =
    norm F σ hσ x + norm F σ hσ y + pairing F σ hσ x y := by
  apply Subtype.ext
  simp only [norm_val, pairing_val, Subfield.coe_add, map_add]
  ring

/-- The additive root transformation in the three coordinates. -/
def rootMap (y : F) : Space F σ →+ Space F σ where
  toFun v := (v.1, v.2.1 + (v.1 : F)*y,
    v.2.2 + pairing F σ hσ v.2.1 y + v.1 * norm F σ hσ y)
  map_zero' := by simp
  map_add' v w := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, Subfield.coe_add]
      ring
    · simp only [Prod.fst_add, Prod.snd_add, pairing_add_left, add_mul]
      abel

@[simp] theorem rootMap_apply (y : F) (t : FixedField F σ) (x : F)
    (z : FixedField F σ) :
    rootMap F σ hσ y (t,x,z) =
      (t,x+(t:F)*y,z+pairing F σ hσ x y+t*norm F σ hσ y) := rfl

theorem rootMap_add_apply (y w : F) (v : Space F σ) :
    rootMap F σ hσ (y+w) v = rootMap F σ hσ y (rootMap F σ hσ w v) := by
  rcases v with ⟨t,x,z⟩
  simp only [rootMap_apply]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ring
  · rw [pairing_add_right, pairing_add_left, pairing_fixed_mul_left, norm_add,
      pairing_comm F σ hσ w y]
    ring

@[simp] theorem rootMap_zero_apply (v : Space F σ) : rootMap F σ hσ 0 v = v := by
  rcases v with ⟨t,x,z⟩
  simp

variable [CharP F 2]

@[simp] theorem pairing_self (x : F) : pairing F σ hσ x x = 0 := by
  apply Subtype.ext
  simp only [pairing_val, CharTwo.add_self_eq_zero, Subfield.coe_zero]

theorem rootMap_involutive (y : F) : Function.Involutive (rootMap F σ hσ y) := by
  intro v
  rw [← rootMap_add_apply, CharTwo.add_self_eq_zero, rootMap_zero_apply]

/-- The root transformation as an additive automorphism. -/
def rootEquiv (y : F) : Space F σ ≃+ Space F σ :=
  { rootMap F σ hσ y with
    invFun := rootMap F σ hσ y
    left_inv := rootMap_involutive F σ hσ y
    right_inv := rootMap_involutive F σ hσ y }

@[simp] theorem rootEquiv_apply (y : F) (v : Space F σ) :
    rootEquiv F σ hσ y v = rootMap F σ hσ y v := rfl

/-- The faithful root subgroup of automorphisms of the additive coordinate group. -/
def rootAction : Multiplicative F →* MulAut (Multiplicative (Space F σ)) where
  toFun y := AddEquiv.toMultiplicative (rootEquiv F σ hσ y.toAdd)
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact rootMap_zero_apply F σ hσ v.toAdd
  map_mul' y w := by
    apply MulEquiv.ext
    intro v
    exact rootMap_add_apply F σ hσ y.toAdd w.toAdd v.toAdd

@[simp] theorem rootAction_apply (y : Multiplicative F) (v : Multiplicative (Space F σ)) :
    (rootAction F σ hσ y v).toAdd = rootMap F σ hσ y.toAdd v.toAdd := rfl

theorem rootAction_injective : Function.Injective (rootAction F σ hσ) := by
  intro y w h
  have he := congrArg (fun e : MulAut (Multiplicative (Space F σ)) =>
    (e (Multiplicative.ofAdd (1,0,0))).toAdd.2.1) h
  simpa using he

/-- The full additive normalizer of the root action. -/
def rootNormalizer : Subgroup (MulAut (Multiplicative (Space F σ))) :=
  Subgroup.normalizer (rootAction F σ hσ).range

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
