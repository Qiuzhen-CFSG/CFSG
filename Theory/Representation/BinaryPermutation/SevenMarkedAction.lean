module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic

/-!
# Extending a prescribed binary A₇ marking

The scalar commutant of the six-dimensional augmentation core is trivial.
Consequently an action agreeing with a prescribed permutation action on a
normal A₇ subgroup agrees on the entire normalizing group. We also compute
the marked transposition difference as the line on the two exchanged letters.

Source: Aschbacher–Smith, B.3 and C.6.4(1), printed pp.167–168.
-/

@[expose] public noncomputable section
open Subgroup Equiv
namespace BinaryPermutation.SevenMarkedAction

def coreAction : Perm (Fin 7) →* MulAut (Multiplicative (core (Fin 7))) where
  toFun g := (LinearEquiv.ofBijective (coreRepresentation (Fin 7) g)
    ((coreRepresentation (Fin 7)).apply_bijective g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 7) 1 v.toAdd) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 7) (g * h) v.toAdd) =
      Multiplicative.ofAdd (coreRepresentation (Fin 7) g (coreRepresentation (Fin 7) h v.toAdd))
    rw [map_mul, Module.End.mul_apply]

theorem coreAction_centralizer (f : MulAut (Multiplicative (core (Fin 7))))
    (hf : ∀ g : alternatingGroup (Fin 7), f * coreAction g.val = coreAction g.val * f) :
    f = 1 := by
  let fAdd : core (Fin 7) ≃+ core (Fin 7) := AddEquiv.toMultiplicative.symm f
  let c : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7) :=
    LinearEquiv.ofBijective (fAdd.toAddMonoidHom.toZModLinearMap 2) fAdd.bijective
  have hc : c = 1 := by
    apply SevenParabolic.linearCentralizer_eq_one
    intro g v
    exact congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (hf g) (Multiplicative.ofAdd v))
  apply MulEquiv.ext
  intro v
  simpa [c, fAdd] using congrArg Multiplicative.ofAdd (DFunLike.congr_fun hc v.toAdd)

/-- An action extending the marked natural A₇ action agrees with the prescribed
permutation action on every normalizing actor. -/
theorem extension_eq {H : Type*} [Group H] (K : Subgroup H) [K.Normal]
    (a : H →* Perm (Fin 7)) (ha : K.map a = alternatingGroup (Fin 7))
    (α : H →* MulAut (Multiplicative (core (Fin 7))))
    (hα : ∀ k : K, α k = coreAction (a k)) : α = coreAction.comp a := by
  ext h : 1
  let β := coreAction.comp a
  let f := (β h)⁻¹ * α h
  have hf : f = 1 := by
    apply coreAction_centralizer
    intro g
    obtain ⟨k,hk,hkg⟩ := (ha.ge g.property)
    let k₀ : K := ⟨k,hk⟩
    have hc := hα ⟨h * k * h⁻¹, (inferInstance : K.Normal).conj_mem k hk h⟩
    change α (h * k * h⁻¹) = β (h * k * h⁻¹) at hc
    have hk' : α k = β k := hα k₀
    have he : f * β k * f⁻¹ = β k := by
      dsimp only [f]
      calc
        (β h)⁻¹ * α h * β k * ((β h)⁻¹ * α h)⁻¹ =
            (β h)⁻¹ * α (h * k * h⁻¹) * β h := by rw [map_mul,map_mul,map_inv, hk']; group
        _ = (β h)⁻¹ * β (h * k * h⁻¹) * β h := by rw [hc]
        _ = β k := by rw [map_mul,map_mul,map_inv]; group
    have he' := mul_inv_eq_iff_eq_mul.mp he
    change f * coreAction (a k) = coreAction (a k) * f at he'
    rwa [hkg] at he'
  exact (inv_mul_eq_one.mp hf).symm

end BinaryPermutation.SevenMarkedAction

namespace BinaryPermutation.SevenMarkedAction

/-- The even-weight vector supported on the marked transposition. -/
def pairVector : core (Fin 7) := ⟨![1,1,0,0,0,0,0], by rw [mem_core]; decide⟩

theorem pairVector_ne_zero : pairVector ≠ 0 := by decide

theorem swap_difference (v : core (Fin 7)) :
    coreRepresentation (Fin 7) (Equiv.swap 0 1) v - v =
      (v.val 0 + v.val 1) • pairVector := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [pairVector, CharTwo.sub_eq_add, Equiv.swap_apply_def]
  all_goals abel

theorem swap_difference_mem (v : core (Fin 7)) :
    Multiplicative.ofAdd (coreRepresentation (Fin 7) (Equiv.swap 0 1) v - v) ∈
      zpowers (Multiplicative.ofAdd pairVector) := by
  rw [swap_difference]
  have hc : v.val 0 + v.val 1 = 0 ∨ v.val 0 + v.val 1 = 1 := by
    exact (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) _
  rcases hc with h | h
  · simp [h]
  · simpa only [h,one_smul] using mem_zpowers (Multiplicative.ofAdd pairVector)

theorem swap_difference_nonzero :
    ∃ v : core (Fin 7),
      coreRepresentation (Fin 7) (Equiv.swap 0 1) v - v = pairVector := by
  refine ⟨⟨![1,0,1,0,0,0,0], by rw [mem_core]; decide⟩, ?_⟩
  rw [swap_difference]
  change (1 + 0 : ZMod 2) • pairVector = pairVector
  simp

theorem pairVector_order : orderOf (Multiplicative.ofAdd pairVector) = 2 := by
  apply orderOf_eq_prime
  · decide
  · exact fun h => pairVector_ne_zero (congrArg Multiplicative.toAdd h)

end BinaryPermutation.SevenMarkedAction
