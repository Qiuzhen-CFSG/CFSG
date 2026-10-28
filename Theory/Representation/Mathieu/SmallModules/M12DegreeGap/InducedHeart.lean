module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction
public import Mathlib.RepresentationTheory.Induced

/-!
# Inducing the marked M₁₁ point module to M₁₂

Use the existing literal `pointEmbedding` and `pointRepresentation`.
Inverse Frobenius reciprocity sends `[g ⊗ w]` to `σ(g⁻¹)(f(w))`.
Evaluation on the identity tensor recovers the original restricted map;
thus a nonzero restricted map gives a surjection onto an irreducible M₁₂
module. The simple-quotient degree bound is a separate finite calculation.

The construction adapts Mathlib's `Rep.indResHomEquiv` (Apache 2.0), as in
the existing M₂₂ reciprocity implementation. Its actual restriction consumer
is assembled in `M12DegreeGap`.
Source context: James, J. Algebra 27 (1973), 57–111; Aschbacher–Smith K.4,
printed p.457.
-/

public noncomputable section
namespace Representation.MathieuSmall.M12DegreeGap
open Sporadic.Mathieu M12Recognition
open Finsupp _root_.TensorProduct

/-- The point module induced along the literal native M₁₁ inclusion. -/
abbrev inducedHeart := Representation.ind pointEmbedding pointRepresentation

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Extend a point-module intertwiner in the inverse-action coinvariant convention. -/
def inducePointMap (σ : Representation (ZMod 2) M12 V)
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) :
    inducedHeart.IntertwiningMap σ :=
  ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => σ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap)
    (fun g ↦ by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [Representation.ofMulAction_single, mul_inv_rev,
        IntertwiningMap.isIntertwining pointRepresentation (σ.comp pointEmbedding) f g]),
    fun g ↦ by ext; simp⟩

/-- The induced map recovers the point map on the identity tensor. -/
theorem inducePointMap_mk_one (σ : Representation (ZMod 2) M12 V)
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) (w : M12Heart) :
    inducePointMap σ f (Representation.IndV.mk pointEmbedding pointRepresentation 1 w) = f w := by
  simp [inducePointMap, Representation.IndV.mk]

/-- A nonzero restricted intertwiner induces a nonzero intertwiner. -/
theorem inducePointMap_ne_zero (σ : Representation (ZMod 2) M12 V)
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) (hf : f ≠ 0) :
    inducePointMap σ f ≠ 0 := by
  intro hz
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  have h := congrArg (fun k => k (Representation.IndV.mk pointEmbedding pointRepresentation 1 w)) hz
  rw [inducePointMap_mk_one] at h
  exact h

/-- Irreducibility makes the actual induced map surjective. -/
theorem inducePointMap_surjective (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding)) (hf : f ≠ 0) :
    Function.Surjective (inducePointMap σ f) :=
  (IsIrreducible.surjective_or_eq_zero _).resolve_right (inducePointMap_ne_zero σ f hf)

end Representation.MathieuSmall.M12DegreeGap
