module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Canonical

/-!
# Additive displacement on the penultimate layer

When the next-next layer vanishes, displacement is additive on the preceding
canonical layer. The native elementary eight is therefore evaluated by its
four kernel and four lift coordinates. This is the transport interface used by
`NativeImage` and leaves the source matrix convention unchanged.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Subgroup Matrix
open scoped Matrix IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB

lemma displacement_mem_layer (C : Subgroup Model) (n : ℕ) (x : Model) (hx : x ∈ C)
    (v : V) (hv : v ∈ layer C n) : displacement x v ∈ layer C (n+1) :=
  Submodule.subset_span ⟨x,hx,v,hv,rfl⟩

lemma displacement_eq_zero_of_layer_zero (C : Subgroup Model) (n : ℕ)
    (hzero : layer C (n+1) = ⊥) (x : Model) (hx : x ∈ C)
    (v : V) (hv : v ∈ layer C n) : displacement x v = 0 := by
  have h := displacement_mem_layer C n x hx v hv
  rwa [hzero,Submodule.mem_bot] at h

/-- Once the next layer is fixed, multiplication becomes addition on displacement. -/
theorem displacement_mul_on_layer (C : Subgroup Model) (n : ℕ)
    (hzero : layer C (n+2) = ⊥) (a b : Model) (ha : a ∈ C) (hb : b ∈ C)
    (v : V) (hv : v ∈ layer C n) :
    displacement (a*b) v = displacement a v + displacement b v := by
  have hz := displacement_eq_zero_of_layer_zero C (n+1) hzero b hb
    (displacement a v) (displacement_mem_layer C n a ha v hv)
  have he : rowAction a v = displacement a v + v := by
    rw [displacement_apply,sub_add_cancel]
  have hm : displacement (a*b) v = displacement b (rowAction a v) + displacement a v := by
    simp only [displacement_apply,rowAction_mul]
    abel
  rw [hm,he,map_add,hz,zero_add,add_comm]

/-- Linear displacement in the elementary actor on the penultimate nonzero layer. -/
def differential (n : ℕ) (hzero : layer (nativeEight 0) (n+2) = ⊥)
    (v : layer (nativeEight 0) n) : Additive (nativeEight 0) →ₗ[ZMod 2] V :=
  AddMonoidHom.toZModLinearMap 2
    { toFun x := displacement (x.toMul : Model) v
      map_zero' := by
        change displacement 1 v = 0
        simp only [displacement_apply,rowAction_apply,map_one,vecMul_one,sub_self]
      map_add' := by
        intro a b
        change displacement ((a.toMul : Model)*(b.toMul : Model)) v = _
        exact displacement_mul_on_layer _ n hzero _ _ a.toMul.property b.toMul.property _ v.property }

theorem differential_apply (n : ℕ) (hzero : layer (nativeEight 0) (n+2) = ⊥)
    (v : layer (nativeEight 0) n) (x : Additive (nativeEight 0)) :
    differential n hzero v x = displacement (x.toMul : Model) v := rfl

/-- Coordinates of the native eight compute its displacement by linearity. -/
theorem differential_coordinates (n : ℕ) (hzero : layer (nativeEight 0) (n+2) = ⊥)
    (v : layer (nativeEight 0) n) (a b : Fin 4 → ZMod 2) :
    displacement ((eightCoordinates 0 (a,b)).toMul : Model) v =
      (∑ i : Fin 4, a i • displacement ((kernelVector 0 i).toMul : Model) v) +
      (∑ i : Fin 4, b i • displacement ((liftVector 0 i).toMul : Model) v) := by
  change differential n hzero v (eightCoordinates 0 (a,b)) = _
  simp only [eightCoordinates,kernelSum,liftSum,map_add,map_sum,map_smul,differential_apply]

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
