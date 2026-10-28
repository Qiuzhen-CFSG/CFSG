module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
-- Internal proof access only for the coordinate-origin equation below.
-- The translation implementation remains private to importing modules.
import all Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The exceptional binary action of the heptad complement

Conjugation through the explicit translation coordinates gives a linear
representation of A7 on F2^4. Evaluating at the binary origin identifies this
representation with the section's actual action on the sixteen complementary
points. The full stabilizer acts affinely in these coordinates. The source
three-cycle is fixed-point-free on nonzero vectors; simplicity of A7 then
proves faithfulness.

Source: Aschbacher--Smith, §5.2, printed p.655; Aschbacher, *Sporadic Groups*,
Chapter 6, Lemma 19.1(5), specialized to the M23 heptad stabilizer.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The origin of the binary coordinates is the point fixed by the section. -/
@[simp] theorem heptadBinaryPoint_zero : heptadBinaryPoint 0 = 0 := by decide +kernel

/-- The binary translations act on the actual ambient points. -/
theorem heptadBinaryEquiv_point (v w : Fin 4 → ZMod 2) :
    ((heptadBinaryEquiv (Multiplicative.ofAdd v) : heptadStabilizer) : M23) •
      heptadBinaryPoint w = heptadBinaryPoint (v + w) := by
  simpa only [heptadKernelComplementAction_apply, heptadBinaryPointEquiv_apply] using
    congrArg Subtype.val (heptadBinaryEquiv_action v w)

/-- The linear action underlying the binary semidirect product. -/
noncomputable def heptadLinearAction : alternatingGroup (Fin 7) →*
    ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) where
  toFun a :=
    { toFun := fun v => (heptadBinaryAction a (Multiplicative.ofAdd v)).toAdd
      invFun := fun v => ((heptadBinaryAction a).symm (Multiplicative.ofAdd v)).toAdd
      left_inv := fun v => (heptadBinaryAction a).left_inv v
      right_inv := fun v => (heptadBinaryAction a).right_inv v
      map_add' := fun v w => congrArg Multiplicative.toAdd
        (map_mul (heptadBinaryAction a) (Multiplicative.ofAdd v) (Multiplicative.ofAdd w))
      map_smul' := by
        intro c v
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
        rcases hc c with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply]
          exact map_one (heptadBinaryAction a)
        · simp only [one_smul, RingHom.id_apply] }
  map_one' := by ext v i; exact congrFun (congrArg Multiplicative.toAdd
      (congrArg (fun f => f (Multiplicative.ofAdd v)) heptadBinaryAction.map_one)) i
  map_mul' a b := by ext v i; exact congrFun (congrArg Multiplicative.toAdd
      (congrArg (fun f => f (Multiplicative.ofAdd v)) (heptadBinaryAction.map_mul a b))) i

@[simp] theorem heptadLinearAction_apply (a : alternatingGroup (Fin 7))
    (v : Fin 4 → ZMod 2) : heptadLinearAction a v =
      (heptadBinaryAction a (Multiplicative.ofAdd v)).toAdd := rfl

/-- Binary coordinates intertwine the complement's ambient point action and its
conjugation representation. -/
theorem heptadLinearAction_point (a : alternatingGroup (Fin 7)) (v : Fin 4 → ZMod 2) :
    heptadBinaryPoint (heptadLinearAction a v) =
      (AlternatingSection.s a : M23) • heptadBinaryPoint v := by
  have origin (w : Multiplicative (Fin 4 → ZMod 2)) :
      (((heptadBinaryEquiv w : heptadStabilizer) : M23) • (0 : Fin 23)) =
        heptadBinaryPoint w.toAdd := by
    rw [← heptadBinaryPoint_zero]
    simpa only [add_zero, ofAdd_toAdd] using heptadBinaryEquiv_point w.toAdd 0
  rw [heptadLinearAction_apply, ← origin, heptadBinaryAction_equivariant]
  rw [heptadConjugation_coe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_smul, mul_smul]
  have hi : (AlternatingSection.s a : M23)⁻¹ • (0 : Fin 23) = 0 := by
    rw [inv_smul_eq_iff, AlternatingSection.s_zero]
  rw [hi, origin]
  rfl

/-- The full action on the complementary sixteen points is the affine action. -/
theorem heptadBinarySplitEquiv_point
    (z : Multiplicative (Fin 4 → ZMod 2) ⋊[heptadBinaryAction] alternatingGroup (Fin 7))
    (w : Fin 4 → ZMod 2) :
    (heptadBinarySplitEquiv z : M23) • heptadBinaryPoint w =
      heptadBinaryPoint (z.left.toAdd + heptadLinearAction z.right w) := by
  rw [heptadBinarySplitEquiv_apply, Subgroup.coe_mul, mul_smul, ← heptadLinearAction_point]
  exact heptadBinaryEquiv_point _ _

/-- Compatibility of the split equivalence with the natural seven-point action. -/
theorem heptadBinarySplitEquiv_label
    (z : Multiplicative (Fin 4 → ZMod 2) ⋊[heptadBinaryAction] alternatingGroup (Fin 7))
    (i : Fin 7) : (heptadBinarySplitEquiv z : M23) • label i =
      label ((z.right : Equiv.Perm (Fin 7)) i) := by
  rw [← heptadAction_apply]
  have h : heptadAction (heptadBinarySplitEquiv z) =
      (z.right : Equiv.Perm (Fin 7)) := heptadAction_split
        ⟨heptadBinaryEquiv z.left, z.right⟩
  rw [h]

/-- Exceptional fixed-point-freeness in additive vector-space notation. -/
theorem heptadLinearAction_cycle_fixed_iff (v : Fin 4 → ZMod 2) :
    heptadLinearAction AlternatingSection.c v = v ↔ v = 0 :=
  heptadBinaryAction_cycle_fixed_iff (Multiplicative.ofAdd v)

/-- This is a faithful four-dimensional binary representation of A7. -/
theorem heptadLinearAction_injective : Function.Injective heptadLinearAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by norm_num :
      5 ≤ Nat.card (Fin 7)) (N := heptadLinearAction.ker) with h | h
  · exact h
  · have hc : heptadLinearAction AlternatingSection.c = 1 := by
      change AlternatingSection.c ∈ heptadLinearAction.ker
      rw [h]
      exact Subgroup.mem_top _
    have hv : heptadLinearAction AlternatingSection.c (fun _ => 1) = (fun _ => 1) := by
      rw [hc]
      rfl
    have hz := (heptadLinearAction_cycle_fixed_iff _).mp hv
    have hz' : (1 : ZMod 2) = 0 := congrFun hz 0
    exact False.elim (one_ne_zero hz')

end Sporadic.Mathieu.M23Geometry
