module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.FixedSpaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Models
public import Theory.Representation.SL2SylowFixedRecognition.Definitions
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The literal binary SL₂ action for 11.3.7

The residual star group acts on the original elementary abelian V_H.
Transport through an actual matrix isomorphism gives a binary representation.
The residual projection, original conjugation and fixed-space kernel are kept
explicit, so that natural quotient coordinates can be returned to the source
without splitting its central extension.

Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace NaturalRecognition
variable {G : Type*} [Group G] (T : Sylow 2 G) (H : Subgroup G)

/-- The literal projection K → K*, retaining the subgroup inclusion. -/
def residualProjection : outsideResidual H →* residualStar T H where
  toFun k := ⟨starProjection T H (inclusion (outsideResidual_le H) k),
    mem_map_of_mem (starProjection T H) k.property⟩
  map_one' := Subtype.ext (map_one (residualStarMap T H))
  map_mul' a b := Subtype.ext (map_mul (residualStarMap T H) a b)

theorem residualProjection_surjective : Function.Surjective (residualProjection T H) := by
  rintro ⟨x,hx⟩
  obtain ⟨h,hh,rfl⟩ := hx
  exact ⟨⟨h,hh⟩,rfl⟩

variable {F : Type*} [Field F]
  [IsElementaryAbelian 2 (omegaClosure T H)]
  (e : residualStar T H ≃* SL(2,F))

/-- Matrix actors act on the additive notation for the original V_H. -/
def binaryAction : Representation (ZMod 2) SL(2,F) (Additive (omegaClosure T H)) where
  toFun g := (starAction T H (e.symm g)).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change starAction T H (e.symm 1) v.toMul = v.toMul
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change starAction T H (e.symm (a*b)) v.toMul =
      starAction T H (e.symm a) (starAction T H (e.symm b) v.toMul)
    simp

theorem binaryAction_equiv (b : residualStar T H) (v : Additive (omegaClosure T H)) :
    (binaryAction T H e (e b) v).toMul = starAction T H b v.toMul := by
  change starAction T H (e.symm (e b)) v.toMul = _
  rw [e.symm_apply_apply]

theorem binaryAction_residual (k : outsideResidual H) (v : Additive (omegaClosure T H)) :
    (binaryAction T H e (e (residualProjection T H k)) v).toMul =
      residualAction T H k v.toMul := by
  rw [binaryAction_equiv]
  rfl

theorem binaryAction_global_fixed (v : Additive (omegaClosure T H)) :
    v ∈ fixedSpace (binaryAction T H e) ⊤ ↔
      (v.toMul : G) ∈ centralizer (outsideResidual H : Set G) := by
  constructor
  · intro hv k hk
    have he := congrArg (fun w : Additive (omegaClosure T H) => (w.toMul : G))
      (hv ⟨e (residualProjection T H ⟨k,hk⟩),mem_top _⟩)
    change ((binaryAction T H e (e (residualProjection T H ⟨k,hk⟩)) v).toMul : G) =
      (v.toMul : G) at he
    rw [binaryAction_residual] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv a
    obtain ⟨k,hk⟩ := residualProjection_surjective T H (e.symm a)
    have ha : a.val = e (residualProjection T H k) := by rw [hk,e.apply_symm_apply]
    change binaryAction T H e a.val v = v
    rw [ha]
    apply Additive.toMul.injective
    rw [binaryAction_residual]
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hv k k.property)

end NaturalRecognition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
