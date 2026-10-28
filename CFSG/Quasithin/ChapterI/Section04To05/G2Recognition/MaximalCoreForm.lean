module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreModule
public import Theory.GroupTheory.ClassTwoCentralPairing

/-!
# The original commutator form on the cubic-core module

The alternating commutator pairing descends to D/D′ with values in the
actual center of D, and takes values in the original marked cubic line.
Its radical is exactly Z(D)/D′, the order-nine plane already constructed.
The full endpoint action and its marked GL₂(3) coordinates preserve this
pairing with their literal action on the value subgroup.

This retains the central-extension data alongside the module, for the
endpoint comparison of Aschbacher–Smith I.4.5, printed p.417. It uses the
standard class-two commutator pairing, with no new model assumptions.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)
/-- The full abelianization carries the original commutator pairing, including its radical. -/
def cubicCommutatorPairing : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →*
    ((cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →* center (cubicOddCore c t.x)) := by
  let := t.maximal_core_central_quotient_elementary
  exact {
    toFun := fun v => (CentralQuotient.pairing (t.cubicCentralProjection v)).comp
      t.cubicCentralProjection
    map_one' := by ext w; simp
    map_mul' := by intro u v; ext w; simp }

@[simp] theorem cubicCommutatorPairing_mk (v w : cubicOddCore c t.x) :
    (t.cubicCommutatorPairing (QuotientGroup.mk' (cubicCoreLine c t.x) v)
      (QuotientGroup.mk' (cubicCoreLine c t.x) w) : cubicOddCore c t.x)=⁅v,w⁆ := by
  let := t.maximal_core_central_quotient_elementary
  change (CentralQuotient.pairing (t.cubicCentralProjection (QuotientGroup.mk' _ v))
    (t.cubicCentralProjection (QuotientGroup.mk' _ w)) : cubicOddCore c t.x)=_
  rw [t.cubicCentralProjection_mk,t.cubicCentralProjection_mk,CentralQuotient.pairing_mk_mk]

/-- The form takes values in the actual marked derived line. -/
theorem cubicCommutatorPairing_line (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    (t.cubicCommutatorPairing v w : cubicOddCore c t.x)∈cubicCoreLine c t.x := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) w
  rw [t.cubicCommutatorPairing_mk,t.cubicCoreLine_eq_commutator hc]
  exact commutator_mem_commutator (mem_top v) (mem_top w)

theorem cubicCommutatorPairing_self (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicCommutatorPairing v v=1 := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  apply Subtype.ext
  rw [t.cubicCommutatorPairing_mk]
  simp

/-- The radical is exactly the original center plane, of order nine. -/
theorem cubicCommutatorPairing_radical (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    (∀ w,t.cubicCommutatorPairing v w=1) ↔ v∈t.cubicCenterPlane := by
  let := t.maximal_core_central_quotient_elementary
  rw [←t.cubicCentralProjection_kernel]
  change (∀ w,CentralQuotient.pairing (t.cubicCentralProjection v)
    (t.cubicCentralProjection w)=1) ↔ t.cubicCentralProjection v=1
  constructor
  · intro h
    apply CentralQuotient.pairing_nondegenerate
    intro w
    obtain ⟨u,rfl⟩ := t.cubicCentralProjection_surjective w
    exact h u
  · intro h w
    rw [h,map_one,MonoidHom.one_apply]

/-- The endpoint action respects the actual commutator, with its action on the marked line. -/
theorem cubicCommutatorPairing_equivariant (a : cubicNormalizer c t.x)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    (t.cubicCommutatorPairing (t.cubicAbelianizationAction a v)
      (t.cubicAbelianizationAction a w) : cubicOddCore c t.x)=
      t.cubicCoreAction a (t.cubicCommutatorPairing v w) := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) w
  rw [t.cubicAbelianizationAction_mk,t.cubicAbelianizationAction_mk,
    t.cubicCommutatorPairing_mk,t.cubicCommutatorPairing_mk,map_commutatorElement]

/-- Both full-core coordinates and their alternating commutator data come from the original group. -/
theorem cubicGLCoreAction_commutator (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (v w : cubicOddCore c t.x) :
    (t.cubicCommutatorPairing
      (QuotientGroup.mk' (cubicCoreLine c t.x) (t.cubicGLCoreAction hc a v))
      (QuotientGroup.mk' (cubicCoreLine c t.x) (t.cubicGLCoreAction hc a w)) : cubicOddCore c t.x)=
      t.cubicGLCoreAction hc a (t.cubicCommutatorPairing
        (QuotientGroup.mk' (cubicCoreLine c t.x) v)
        (QuotientGroup.mk' (cubicCoreLine c t.x) w)) := by
  rw [t.cubicCommutatorPairing_mk,t.cubicCommutatorPairing_mk,map_commutatorElement]

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
