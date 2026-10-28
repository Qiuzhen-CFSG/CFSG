module
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.Mathieu.M22.Properties.InvolutionClasses
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace Sporadic.Mathieu
noncomputable section
/-- A finite C12 interface for the Atlas Schur-multiplier datum. This does not identify the actual Schur multiplier or a universal central extension. -/
public abbrev M22SchurMultiplier := Multiplicative (ZMod 12)
public theorem m22SchurMultiplier_order : Nat.card M22SchurMultiplier = 12 := by
  exact Nat.card_zmod 12
@[expose] public def m22MultiplierInversion : M22SchurMultiplier ≃* M22SchurMultiplier where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [mul_comm]
public theorem m22MultiplierInversion_sq (x : M22SchurMultiplier) :
    m22MultiplierInversion (m22MultiplierInversion x) = x := by
  simp [m22MultiplierInversion]
public abbrev M22CoverModel (n : Nat) := M22 × Multiplicative (ZMod n)
@[expose] public def m22CoverProjection (n : Nat) : M22CoverModel n →* M22 where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
@[expose] public def m22CoverLift (n : Nat) : M22 →* M22CoverModel n where
  toFun x := (x, 1)
  map_one' := rfl
  map_mul' _ _ := by simp
public theorem m22CoverProjection_surjective (n : Nat) :
    Function.Surjective (m22CoverProjection n) := by
  intro g
  exact ⟨(g, 1), rfl⟩
public theorem m22CoverProjection_lift (n : Nat) :
    (m22CoverProjection n).comp (m22CoverLift n) = MonoidHom.id M22 := by
  apply MonoidHom.ext
  intro g
  rfl
public theorem m22CoverModel_order (n : Nat) :
    Nat.card (M22CoverModel n) = 443520 * n := by
  rw [Nat.card_prod, m22_order]
  have hz : Nat.card (Multiplicative (ZMod n)) = n := Nat.card_zmod n
  rw [hz]
public structure M22CoverInterface where
  label : String
  kernelOrder : Nat
  quotientOrder : Nat
  splitModelOrder : Nat
  order_formula : splitModelOrder = 443520 * kernelOrder
@[expose] public def m22TwoCoverInterface : M22CoverInterface :=
  { label := "2M22 (split interface)", kernelOrder := 2,
    quotientOrder := 443520, splitModelOrder := 887040, order_formula := by norm_num }
@[expose] public def m22ThreeCoverInterface : M22CoverInterface :=
  { label := "3M22 (split interface)", kernelOrder := 3,
    quotientOrder := 443520, splitModelOrder := 1330560, order_formula := by norm_num }
@[expose] public def m22FourCoverInterface : M22CoverInterface :=
  { label := "4M22 (split interface)", kernelOrder := 4,
    quotientOrder := 443520, splitModelOrder := 1774080, order_formula := by norm_num }
public theorem m22CoverInterface_orders :
    (m22TwoCoverInterface.splitModelOrder,
      m22ThreeCoverInterface.splitModelOrder,
      m22FourCoverInterface.splitModelOrder) =
      (887040, 1330560, 1774080) := by rfl
end
end Sporadic.Mathieu
