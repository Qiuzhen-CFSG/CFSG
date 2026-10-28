module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Model
public import Theory.Representation.SL2.BinaryHermitianRecognition.TensorProduct

/-!
# Marked rank-one models from actual intertwiners

The binary natural and Hermitian recognition predicates retain representation
equivalences. Here those maps construct the marked models used by the K.3
calculations on the original layer. In the Hermitian branch the field
identification is included in the group marking; the existing quadratic
isometry then compares the action with the literal minus Omega action.
The re-exported scalar-extension equivalence identifies its model over the
quadratic field with the actual tensor N ⊗ N^σ, including exponent one.

Source: Aschbacher–Smith, K.3.1, printed pp.453–454.
-/

public section

open scoped MatrixGroups TensorProduct
open Representation Representation.SL2
namespace CFSG.Quasithin.ChapterK.RankOne
noncomputable section
variable {G V K : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field K] [Finite K] [CharP K 2]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

local instance : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance recognitionHermitianBinarySpace (s : ℕ) [NeZero s] :
    Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space s) :=
  BinarySmall.spaceBinaryModule s

/-- An actual natural intertwiner gives the marked model used by K.3.1.1. -/
def naturalModelOfIsNatural (e : L ≃* SL(2,K))
    (hn : BinarySmall.IsNatural ((ρ.comp L.subtype).comp e.symm.toMonoidHom)) :
    NaturalModel (F := K) ρ L := by
  let φ := hn.some
  refine ⟨e, φ.toLinearEquiv, ?_⟩
  intro g v
  have hh := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (e g) v
  change φ.toLinearEquiv (ρ (e.symm (e g) : G) v) =
    Matrix.mulVec (e g).val (φ.toLinearEquiv v) at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

private def sl2FieldEquiv {F : Type*} [Field F] (e : K ≃+* F) : SL(2,K) ≃* SL(2,F) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply (g i j)
  right_inv g := by ext i j; exact e.apply_symm_apply (g i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

/-- The recognized Hermitian field and intertwiner give the existing
orthogonal model, so its literal minus-Omega comparison applies. -/
def orthogonalModelOfIsHermitian (e : L ≃* SL(2,K)) {s : ℕ} [NeZero s]
    (hh : BinarySmall.IsHermitian ((ρ.comp L.subtype).comp e.symm.toMonoidHom) s) :
    OrthogonalModel s ρ L := by
  let f := hh.choose
  let φ := hh.choose_spec.some
  refine ⟨e.trans (sl2FieldEquiv f), φ.toLinearEquiv, ?_⟩
  intro g v
  have ht := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (e g) v
  change φ.toLinearEquiv (ρ (e.symm (e g) : G) v) =
    BinarySmall.hermitian s (e.trans (sl2FieldEquiv f) g) (φ.toLinearEquiv v) at ht
  simpa only [MulEquiv.symm_apply_apply] using ht

end
end CFSG.Quasithin.ChapterK.RankOne
