module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SignedAction
public import Theory.Representation.BinaryAlternatingDualCoreCohomology
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of lifted six-letter alternating actions

Two actions on the even Clifford group inducing the same literal augmentation
core action differ by binary linear sign functionals. Their discrepancies form
a cocycle in the contragredient core after inverting the actor. Vanishing of
first cohomology makes this cocycle principal; its functional gives an explicit
sign-change automorphism conjugating the lifted action to the intrinsic signed
permutation action. This automorphism fixes the sign kernel pointwise, but its
value on the constant vector may make it invert the volume generator.

Source: the split-extension calculation in Aschbacher–Smith I.2.2(6), printed
pp.410 and 412 / PDF pp.421 and 423, combined manuscript of 1 March 2004.
The target action is the intrinsic signed formula, independent of any radical.
-/

@[expose] public section

open BinaryPermutation
namespace EvenCliffordSix

/-- A binary linear sign change over the literal core. -/
def signChange (f : V →ₗ[F] F) : MulAut Model where
  toFun x := ⟨x.sign + f x.vector, x.vector⟩
  invFun x := ⟨x.sign + f x.vector, x.vector⟩
  left_inv x := by
    apply Model.ext
    · change x.sign + f x.vector + f x.vector = x.sign
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rfl
  right_inv x := by
    apply Model.ext
    · change x.sign + f x.vector + f x.vector = x.sign
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rfl
  map_mul' x y := by
    apply Model.ext
    · change x.sign + y.sign + cocycle x.vector.val y.vector.val + f (x.vector + y.vector) =
        (x.sign + f x.vector) + (y.sign + f y.vector) + cocycle x.vector.val y.vector.val
      rw [map_add]
      abel
    · rfl

@[simp]theorem signChange_projection (f : V →ₗ[F] F) (x : Model) :
    projection (signChange f x) = projection x := rfl

@[simp]theorem signChange_centralSign (f : V →ₗ[F] F) (c : F) :
    signChange f (centralSign c) = centralSign c := by
  apply Model.ext
  · change c + f 0 = c
    simp
  · rfl

@[simp]theorem signChange_involution (f : V →ₗ[F] F) :
    signChange f involution = involution := signChange_centralSign f 1

/-- The value of the correcting functional on the constant vector records
whether the volume is fixed. -/
theorem signChange_volume_eq_iff (f : V →ₗ[F] F) :
    signChange f volume = volume ↔ f volumeVector = 0 := by
  constructor
  · intro h
    have hs := congrArg Model.sign h
    change 0 + f volumeVector = 0 at hs
    simpa only [zero_add] using hs
  · intro h
    apply Model.ext
    · change 0 + f volumeVector = 0
      rw [h, add_zero]
    · rfl

theorem signChange_volume (f : V →ₗ[F] F) :
    signChange f volume = volume ∨ signChange f volume = volume⁻¹ := by
  have hc : ∀ c : F, c = 0 ∨ c = 1 := by decide
  rcases hc (f volumeVector) with h | h
  · left
    apply Model.ext
    · change 0 + f volumeVector = 0
      rw [h, add_zero]
    · rfl
  · right
    apply Model.ext
    · change 0 + f volumeVector = 0 + cocycle volumeVector.val volumeVector.val
      rw [h]
      have hv := congrArg Model.sign volume_sq
      simpa only [pow_two, mul_sign, volume, involution, centralSign, zero_add] using hv.symm
    · rfl

variable (ψ : A →* MulAut Model)
variable (hψ : ∀ a x, (projection (ψ a x)).toAdd =
  coreRepresentation (Fin 6) a.val (projection x).toAdd)
include hψ

theorem liftedAction_centralSign (a : A) (c : F) : ψ a (centralSign c) = centralSign c := by
  have hi : ψ a involution = involution := by
    have hv : ψ a involution ∈ signKernel := by
      change (projection (ψ a involution)).toAdd = 0
      rw [hψ]
      exact map_zero _
    rcases (mem_signKernel_iff _).mp hv with h | h
    · have hz : involution = 1 := (ψ a).injective (h.trans (map_one (ψ a)).symm)
      exact (involution_ne_one hz).elim
    · exact h
  have hc : ∀ c : F, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · exact map_one (ψ a)
  · exact hi

theorem liftedAction_sign (a : A) (x : Model) :
    (ψ a x).sign = x.sign + (ψ a ⟨0, x.vector⟩).sign := by
  have hx : x = centralSign x.sign * (⟨0, x.vector⟩ : Model) := by
    rw [centralSign_mul]
    exact Model.ext (add_zero _).symm rfl
  conv_lhs => rw [hx, map_mul, liftedAction_centralSign ψ hψ, centralSign_mul]

omit hψ in
theorem intrinsic_sign (a : A) (x : Model) :
    (action a x).sign = x.sign + (action a ⟨0, x.vector⟩).sign :=
  liftedAction_sign action (fun _ _ => rfl) a x

/-- The sign discrepancy of two lifts, as a functional on the core. -/
def actionDifference (a : A) : V →ₗ[F] F where
  toFun v := (ψ a ⟨0, v⟩).sign - (action a ⟨0, v⟩).sign
  map_add' v w := by
    have hp := congrArg Model.sign (map_mul (ψ a) (⟨0,v⟩ : Model) ⟨0,w⟩)
    have hq := congrArg Model.sign (map_mul (action a) (⟨0,v⟩ : Model) ⟨0,w⟩)
    rw [liftedAction_sign ψ hψ a] at hp
    rw [intrinsic_sign a] at hq
    simp only [mul_sign, mul_vector, zero_add] at hp hq
    have hv := hψ a (⟨0,v⟩ : Model)
    have hw := hψ a (⟨0,w⟩ : Model)
    change (ψ a ⟨0,v⟩).vector = (action a ⟨0,v⟩).vector at hv
    change (ψ a ⟨0,w⟩).vector = (action a ⟨0,w⟩).vector at hw
    rw [hv, hw] at hp
    linear_combination hp - hq
  map_smul' c v := by
    have hc : ∀ c : F, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      change (ψ a 1).sign - (action a 1).sign = 0
      rw [map_one, map_one, sub_self]
    · simp

theorem actionDifference_apply (a : A) (x : Model) :
    actionDifference ψ hψ a x.vector = (ψ a x).sign - (action a x).sign := by
  change (ψ a ⟨0, x.vector⟩).sign - (action a ⟨0, x.vector⟩).sign = _
  rw [liftedAction_sign ψ hψ a x, intrinsic_sign a x]
  abel

theorem liftedAction_eq_signChange (a : A) (x : Model) :
    ψ a x = action a (signChange (actionDifference ψ hψ a) x) := by
  apply Model.ext
  · rw [intrinsic_sign]
    change (ψ a x).sign = (x.sign + actionDifference ψ hψ a x.vector) +
      (action a ⟨0,x.vector⟩).sign
    rw [actionDifference_apply, intrinsic_sign a x]
    abel
  · exact hψ a x

end EvenCliffordSix

namespace EvenCliffordSix
open BinaryPermutation Representation.OneCohomology
variable (ψ : A →* MulAut Model)
variable (hψ : ∀ a x, (projection (ψ a x)).toAdd =
  coreRepresentation (Fin 6) a.val (projection x).toAdd)
include hψ

theorem actionDifference_mul (a b : A) (v : V) :
    actionDifference ψ hψ (a * b) v =
      actionDifference ψ hψ a (coreRepresentation (Fin 6) b.val v) +
        actionDifference ψ hψ b v := by
  let x : Model := ⟨0, v⟩
  have hp : (ψ b x).vector = (action b x).vector := hψ b x
  have hd := actionDifference_apply ψ hψ a (ψ b x)
  rw [intrinsic_sign a (ψ b x), hp] at hd
  have hab := actionDifference_apply ψ hψ (a * b) x
  have hb := actionDifference_apply ψ hψ b x
  rw [map_mul, map_mul] at hab
  change actionDifference ψ hψ (a * b) v =
    (ψ a (ψ b x)).sign - (action a (action b x)).sign at hab
  rw [intrinsic_sign a (action b x)] at hab
  change actionDifference ψ hψ a (coreRepresentation (Fin 6) b.val v) = _ at hd
  change actionDifference ψ hψ b v = _ at hb
  linear_combination hab - hd - hb

/-- Inverting the actor converts the right discrepancy law into the standard
contragredient cocycle convention. -/
def differenceCocycle :
    cocycles (alternatingCoreRepresentation (Fin 6)).dual :=
  ⟨fun a => actionDifference ψ hψ a⁻¹, by
    intro a b
    ext v
    change actionDifference ψ hψ (a * b)⁻¹ v =
      actionDifference ψ hψ b⁻¹ (coreRepresentation (Fin 6) a⁻¹.val v) +
        actionDifference ψ hψ a⁻¹ v
    rw [mul_inv_rev, actionDifference_mul]⟩

/-- Every lift of the literal core action is conjugate over that core to the
intrinsic signed action. The correcting automorphism fixes the binary sign
kernel, and may invert the volume generator. -/
theorem exists_action_comparison : ∃ T : MulAut Model,
    (∀ x, projection (T x) = projection x) ∧
    (∀ a x, T (ψ a x) = action a (T x)) ∧
    T involution = involution ∧
    (T volume = volume ∨ T volume = volume⁻¹) ∧
    (∀ x ∈ signKernel, T x = x) := by
  obtain ⟨f, hf⟩ := alternatingCore_dual_principal_surjective 6 (Or.inl rfl)
    (differenceCocycle ψ hψ)
  refine ⟨signChange f, signChange_projection f, ?_, signChange_involution f,
    signChange_volume f, ?_⟩
  · intro a x
    have h := congrArg (fun c : cocycles (alternatingCoreRepresentation (Fin 6)).dual =>
      c.val a⁻¹ x.vector) hf
    change f (coreRepresentation (Fin 6) (a⁻¹)⁻¹.val x.vector) - f x.vector =
      actionDifference ψ hψ (a⁻¹)⁻¹ x.vector at h
    simp only [inv_inv] at h
    rw [actionDifference_apply] at h
    apply Model.ext
    · change (ψ a x).sign + f (ψ a x).vector = (action a (signChange f x)).sign
      rw [intrinsic_sign]
      have hv : (ψ a x).vector = coreRepresentation (Fin 6) a.val x.vector := hψ a x
      rw [intrinsic_sign a x] at h
      rw [hv]
      change (ψ a x).sign + f (coreRepresentation (Fin 6) a.val x.vector) =
        (x.sign + f x.vector) + (action a ⟨0,x.vector⟩).sign
      rw [CharTwo.sub_eq_add] at h
      rw [← eq_sub_iff_add_eq.mp h]
      calc
        _ = ((x.sign + f x.vector) + (action a ⟨0,x.vector⟩).sign) +
            (f (coreRepresentation (Fin 6) a.val x.vector) +
              f (coreRepresentation (Fin 6) a.val x.vector)) := by abel
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
    · exact hψ a x
  · intro x hx
    have he : x = centralSign x.sign := Model.ext rfl ((mem_signKernel x).mp hx)
    rw [he, signChange_centralSign]
end EvenCliffordSix
