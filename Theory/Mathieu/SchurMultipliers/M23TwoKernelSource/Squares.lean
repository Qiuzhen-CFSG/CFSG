module

public import Theory.GroupTheory.CentralDoubleCoverFusion
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.Mathieu.SchurMultipliers.OddLocalPartialInversion
public import Theory.ElementaryAbelian.Basic

/-!
# Involution lifts in central double covers of native M₂₃

The actual binary heptad translations contain an elementary eight-group.
The proved single involution class and the central-extension square pairing
therefore force every involution lift to have square one. In particular the
full preimage of the actual translation group is elementary abelian.

These are the local inputs for the marked heptad splitting argument. The
kernel map, native design group and original heptad inclusion are retained.
Source: the M₂₃ multiplier entry of Aschbacher–Smith I.1.3, printed p.407,
and the native heptad geometry of 5.2.21, printed p.657.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering
open Theory.GroupTheory
namespace Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
open M23Geometry

private def eightToFour :
    Multiplicative (Fin 3 → ZMod 2) →* Multiplicative (Fin 4 → ZMod 2) where
  toFun v := Multiplicative.ofAdd (fun i => if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0)
  map_one' := by
    change (fun i : Fin 4 => if h : i.val < 3 then (0 : Fin 3 → ZMod 2) ⟨i.val, h⟩ else 0) = 0
    ext i
    split_ifs <;> rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    change (if h : i.val < 3 then (v.toAdd + w.toAdd) ⟨i.val, h⟩ else 0) =
      (if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0) +
      (if h : i.val < 3 then w.toAdd ⟨i.val, h⟩ else 0)
    split_ifs <;> simp

private theorem eightToFour_injective : Function.Injective eightToFour := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have he := congrArg (fun x : Multiplicative (Fin 4 → ZMod 2) => x.toAdd i.castSucc) h
  change (if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0) =
    (if h : i.val < 3 then w.toAdd ⟨i.val, h⟩ else 0) at he
  simpa only [dif_pos i.isLt] using he

private def nativeEight : Multiplicative (Fin 3 → ZMod 2) →* M23 :=
  heptadStabilizer.subtype.comp
    (heptadKernel.subtype.comp (heptadBinaryEquiv.toMonoidHom.comp eightToFour))

private theorem nativeEight_injective : Function.Injective nativeEight :=
  heptadStabilizer.subtype_injective.comp
    (heptadKernel.subtype_injective.comp
      (heptadBinaryEquiv.injective.comp eightToFour_injective))

/-- Every lift of a square-one native M₂₃ element has square one in a
central double cover. This includes the central fiber itself. -/
theorem involution_lift_square {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : E) (hx : (f.toMonoidHom x) ^ 2 = 1) : x ^ 2 = 1 :=
  CentralDoubleCoverFusion.square_eq_one_of_double_cover f.toMonoidHom f.surjective
    f.ker_le_center hcard nativeEight nativeEight_injective involutions_isConj x hx

/-- The full preimage of the actual heptad translations is elementary
abelian; this is a subgroup of the original covering group. -/
theorem translation_preimage_elementary {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    IsElementaryAbelian 2
      ((heptadKernel.map heptadStabilizer.subtype).comap f.toMonoidHom) := by
  let N := (heptadKernel.map heptadStabilizer.subtype).comap f.toMonoidHom
  have hs (x : N) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply involution_lift_square f hcard
    obtain ⟨v, hv, he⟩ := x.property
    rw [← he, ← map_pow]
    have hv2 : v ^ 2 = 1 := by
      have h := heptadKernel_sq ⟨v, hv⟩
      exact congrArg Subtype.val h
    rw [hv2, map_one]
  have hi (x : N) : x⁻¹ = x :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hs x)
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hi, hi]

end Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
