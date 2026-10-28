module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.OrthogonalQuotient

/-!
# The cubic fixed points in the short-root eight-group

Over the binary fixed field, the cubic fixes exactly the identity and the
marked short-root involution in the elementary eight-group. This matrix
calculation is the fixed-point input for the F.4.42 central lift.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

theorem binary_orthogonal_cubic_fixed
    (hc : Nat.card (FixedBy.subfield F σ) = 2)
    (X : hermitianMatrices F σ) (hX : X ∈ fixedHermitian F σ)
    (hf : hermitianCongruence F σ hσ (cubic F) X = X) :
    X = 0 ∨ X = shortParameter F σ := by
  have he := (cubic_fixed_iff F σ hσ X).mp hf
  let b : FixedBy.subfield F σ := ⟨X.val 0 1,hX 0 1⟩
  by_cases hb : b = 0
  · have hb0 : X.val 0 1 = 0 := congrArg Subtype.val hb
    left
    rw [he,hb0]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fixedParameter]
  · have hb1 : X.val 0 1 = 1 := congrArg Subtype.val
      (((Nat.card_eq_two_iff' (0 : FixedBy.subfield F σ)).mp hc).unique hb one_ne_zero)
    right
    rw [he,hb1,fixedParameter_one]

variable [Finite F]
local notation "X" => shortCentralizer F σ hσ
local notation "V" => orthogonalRadical F σ hσ

def markedCubic : X := fixedLevi F σ hσ ⟨cubic F,cubic_mem_fixedSL F σ⟩

def markedShort : X := radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd (shortParameter F σ))

theorem binary_orthogonal_cubic_centralizer
    (hc : Nat.card (FixedBy.subfield F σ) = 2)
    (x : X) (hx : x.val ∈ V)
    (hxc : x * markedCubic F σ hσ = markedCubic F σ hσ * x) :
    x = 1 ∨ x = markedShort F σ hσ := by
  obtain ⟨Y,hY,he⟩ := hx
  have hxe : radicalIntoCentralizer F σ hσ Y = x := Subtype.ext he
  have hconj : markedCubic F σ hσ * x * (markedCubic F σ hσ)⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr hxc.symm
  rw [← hxe,radicalIntoCentralizer_conj] at hconj
  have hrad : Function.Injective (radicalIntoCentralizer F σ hσ) :=
    (inclusion_injective (radical_le_shortCentralizer F σ hσ)).comp (radicalEquiv F σ hσ).injective
  have hy : hermitianCongruence F σ hσ (cubic F) Y.toAdd = Y.toAdd := by
    have h := congrArg Multiplicative.toAdd (hrad hconj)
    simpa only [toAdd_ofAdd,markedCubic,fixedLevi,factorRestriction_levi] using h
  obtain h0 | ht := binary_orthogonal_cubic_fixed F σ hσ hc Y.toAdd hY hy
  · left
    rw [← hxe,show Y = 1 from congrArg Multiplicative.ofAdd h0,map_one]
  · right
    rw [← hxe,show Y = Multiplicative.ofAdd (shortParameter F σ) from congrArg Multiplicative.ofAdd ht]
    rfl
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
