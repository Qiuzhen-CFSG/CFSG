module

public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Coordinates
public import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Ring

/-!
# The solvable kernel of the unitary root-parameter action

An additive automorphism centralizing all roots has one common fixed-field
scalar on the three diagonal blocks. Its remaining blocks are a compatible
pair of shears and one arbitrary additive map from the first fixed-field
coordinate to the last. The kernel of the scalar homomorphism is abelian,
so the full parameter-action kernel is solvable. This is the kernel step
in the unitary-four Sylow automorphism argument of Aschbacher--Smith F.1.11
and F.1.12.
-/

open scoped IsMulCommutative
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer

variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

abbrev ParameterKernel := (parameterAction F σ hσ).ker

theorem parameterEquiv_kernel (g : ParameterKernel F σ hσ) (y : F) :
    parameterEquiv F σ hσ g.val y = y := by
  have hh := congrArg (fun e : MulAut (Multiplicative F) => e (Multiplicative.ofAdd y)) g.property
  exact congrArg Multiplicative.toAdd hh

def kernelScalarValue (g : ParameterKernel F σ hσ) : FixedField F σ := topMap F σ hσ g.val 1

def kernelVector (g : ParameterKernel F σ hσ) : F :=
  (normalizerEquiv F σ hσ g.val (1,0,0)).2.1

def kernelShear (g : ParameterKernel F σ hσ) : FixedField F σ →+ FixedField F σ where
  toFun t := (normalizerEquiv F σ hσ g.val (t,0,0)).2.2
  map_zero' := by
    exact congrArg (fun v : Space F σ => v.2.2) (normalizerEquiv F σ hσ g.val).map_zero
  map_add' t u := by
    simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add] using
      congrArg (fun v : Space F σ => v.2.2) ((normalizerEquiv F σ hσ g.val).map_add (t,0,0) (u,0,0))

@[simp] theorem kernelShear_apply (g : ParameterKernel F σ hσ) (t : FixedField F σ) :
    kernelShear F σ hσ g t = (normalizerEquiv F σ hσ g.val (t,0,0)).2.2 := rfl

theorem kernel_topMap (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ)
    (t : FixedField F σ) : topMap F σ hσ g.val t = kernelScalarValue F σ hσ g * t := by
  have hh := middleMap_fixed_mul F σ hσ hnt g.val t 1
  rw [middleMap_eq F σ hσ hnt, parameterEquiv_kernel, parameterEquiv_kernel] at hh
  apply Subtype.ext
  simpa only [mul_one, Subfield.coe_mul, kernelScalarValue] using hh.symm

theorem kernel_middleMap (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ) (x : F) :
    middleMap F σ hσ g.val x = (kernelScalarValue F σ hσ g : F) * x := by
  rw [middleMap_eq F σ hσ hnt, parameterEquiv_kernel]
  rfl

theorem kernel_centralMap (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ)
    (z : FixedField F σ) : centralMap F σ hσ g.val z = kernelScalarValue F σ hσ g * z := by
  obtain ⟨y,rfl⟩ := pairing_one_surjective F σ hσ hnt z
  rw [centralMap_pairing F σ hσ hnt, kernel_middleMap F σ hσ hnt,
    parameterEquiv_kernel, pairing_fixed_mul_left]

theorem kernel_lowerShift (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ) (x : F) :
    (normalizerEquiv F σ hσ g.val (0,x,0)).2.2 = pairing F σ hσ (kernelVector F σ hσ g) x := by
  have hh := normalizer_norm_equation F σ hσ g.val 1 x
  rw [kernel_centralMap F σ hσ hnt, parameterEquiv_kernel] at hh
  simp only [Subfield.coe_one, one_mul] at hh
  exact add_right_cancel hh

theorem kernel_upperShift (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ)
    (t : FixedField F σ) :
    (normalizerEquiv F σ hσ g.val (t,0,0)).2.1 = (t:F) * kernelVector F σ hσ g := by
  apply CharTwo.add_eq_zero.mp
  apply pairing_nondegenerate F σ hσ hnt
  intro y
  have hh := normalizer_norm_equation F σ hσ g.val t y
  rw [kernel_lowerShift F σ hσ hnt, kernel_centralMap F σ hσ hnt,
    kernel_topMap F σ hσ hnt, parameterEquiv_kernel, pairing_fixed_mul_right] at hh
  have hp : t * pairing F σ hσ (kernelVector F σ hσ g) y =
      pairing F σ hσ (normalizerEquiv F σ hσ g.val (t,0,0)).2.1 y := by
    rw [mul_assoc (kernelScalarValue F σ hσ g) t (norm F σ hσ y)] at hh
    exact add_right_cancel hh
  rw [pairing_add_left, pairing_fixed_mul_left, ← hp]
  apply Subtype.ext
  exact CharTwo.add_self_eq_zero _

/-- The parameter centralizer consists of a common fixed-field scalar and
two compatible shears. Its last free shear is an arbitrary additive map on `K`. -/
theorem kernel_normal_form (hnt : ∃ u, σ u ≠ u) (g : ParameterKernel F σ hσ)
    (t : FixedField F σ) (x : F) (z : FixedField F σ) :
    normalizerEquiv F σ hσ g.val (t,x,z) =
      (kernelScalarValue F σ hσ g * t,
        (kernelScalarValue F σ hσ g : F)*x + (t:F)*kernelVector F σ hσ g,
        kernelScalarValue F σ hσ g*z + pairing F σ hσ (kernelVector F σ hσ g) x +
          kernelShear F σ hσ g t) := by
  apply Prod.ext
  · rw [normalizer_top F σ hσ hnt, kernel_topMap F σ hσ hnt]
  apply Prod.ext
  · rw [normalizer_middle_coordinate F σ hσ hnt, kernel_upperShift F σ hσ hnt,
      kernel_middleMap F σ hσ hnt]
    exact add_comm _ _
  · rw [normalizer_last_coordinate, kernel_lowerShift F σ hσ hnt,
      kernel_centralMap F σ hσ hnt]
    rw [kernelShear_apply]
    abel

/-- The scalar quotient of the parameter-action kernel. -/
def kernelScalar (hnt : ∃ u, σ u ≠ u) : ParameterKernel F σ hσ →* (FixedField F σ)ˣ where
  toFun g := Units.mk0 (kernelScalarValue F σ hσ g) (topMap_one_ne_zero F σ hσ hnt g.val)
  map_one' := by apply Units.ext; rfl
  map_mul' g h := by
    apply Units.ext
    change (normalizerEquiv F σ hσ g.val (normalizerEquiv F σ hσ h.val (1,0,0))).1 =
      kernelScalarValue F σ hσ g * kernelScalarValue F σ hσ h
    rw [normalizer_top F σ hσ hnt, kernel_topMap F σ hσ hnt]
    rfl

theorem kernelScalar_ker_isMulCommutative (hnt : ∃ u, σ u ≠ u) :
    IsMulCommutative (kernelScalar F σ hσ hnt).ker := by
  refine ⟨⟨fun g h => ?_⟩⟩
  have hg : kernelScalarValue F σ hσ g.val = 1 := congrArg Units.val g.property
  have hh : kernelScalarValue F σ hσ h.val = 1 := congrArg Units.val h.property
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  change normalizerEquiv F σ hσ g.val.val (normalizerEquiv F σ hσ h.val.val v.toAdd) =
    normalizerEquiv F σ hσ h.val.val (normalizerEquiv F σ hσ g.val.val v.toAdd)
  rcases v.toAdd with ⟨t,x,z⟩
  simp only [kernel_normal_form F σ hσ hnt, hg, hh, one_mul, Subfield.coe_one,
    pairing_add_right, pairing_fixed_mul_right]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ring
  · rw [pairing_comm F σ hσ (kernelVector F σ hσ h.val) (kernelVector F σ hσ g.val)]
    abel

/-- Automorphisms centralizing every root parameter form a solvable group. -/
theorem parameterKernel_isSolvable (hnt : ∃ u, σ u ≠ u) :
    Group.IsSolvable (ParameterKernel F σ hσ) := by
  let : IsMulCommutative (kernelScalar F σ hσ hnt).ker :=
    kernelScalar_ker_isMulCommutative F σ hσ hnt
  exact Group.isSolvable_of_ker_le_range (kernelScalar F σ hσ hnt).ker.subtype
    (kernelScalar F σ hσ hnt) (by rw [Subgroup.range_subtype])

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
