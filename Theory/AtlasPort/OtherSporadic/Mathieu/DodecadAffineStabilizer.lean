/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFifthFixed
public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAction

/-!
# DodecadAffineStabilizer

The subgroup of a tetrad affine stabilizer fixing a parametrized dodecad is identified
with the actual coordinate stabilizer. Decoding a fixed word shows that its linear
projection lands in the corresponding fixed-word Klein kernel.

Source: `Atlas/Mathieu/DodecadAffineStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def dodecadAffineStabilizer (i : HexIndex) (p : DodecadParameters i) : Subgroup (TetradPointAffine i) :=
  (MulAction.stabilizer (TetradPointStabilizer i) (dodecadParametersSupport i p).val).comap
    (tetradPointStabilizerEquiv i).toMonoidHom

theorem dodecadAffineStabilizer_mem (i : HexIndex) (p : DodecadParameters i) (x : TetradPointAffine i) :
    x ∈ dodecadAffineStabilizer i p ↔
      coordinatePermutation (affinePermutation x.left.toAdd.val.val x.right.val.val.val)
        (c0Encoder (p.1.val.val,p.2.val)) = c0Encoder (p.1.val.val,p.2.val) := by
  change ((tetradPointStabilizerEquiv i x).val • (dodecadParametersSupport i p).val =
    (dodecadParametersSupport i p).val) ↔ _
  constructor
  · intro he
    apply support_injective
    exact (coordinatePermutation_support _ _).trans (congrArg Subtype.val he)
  · intro he
    apply Subtype.ext
    exact (coordinatePermutation_support _ _).symm.trans (congrArg support he)

def dodecadAffineActualEquiv (i : HexIndex) (p : DodecadParameters i) :
    dodecadAffineStabilizer i p ≃*
      MulAction.stabilizer (TetradPointStabilizer i) (dodecadParametersSupport i p).val where
  toFun x := ⟨tetradPointStabilizerEquiv i x.val,x.prop⟩
  invFun x := ⟨(tetradPointStabilizerEquiv i).symm x.val,by
    change tetradPointStabilizerEquiv i ((tetradPointStabilizerEquiv i).symm x.val) ∈
      MulAction.stabilizer (TetradPointStabilizer i) (dodecadParametersSupport i p).val
    rw [MulEquiv.apply_symm_apply]
    exact x.prop⟩
  left_inv x := Subtype.ext ((tetradPointStabilizerEquiv i).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((tetradPointStabilizerEquiv i).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((tetradPointStabilizerEquiv i).map_mul x.val y.val)

def dodecadAffineProjection (i : HexIndex) (p : DodecadParameters i) :
    dodecadAffineStabilizer i p →* hexPointKernel i :=
  SemidirectProduct.rightHom.comp (dodecadAffineStabilizer i p).subtype

theorem dodecadAffineProjection_fixed (i : HexIndex) (p : DodecadParameters i)
    (x : dodecadAffineStabilizer i p) :
    hexZeroLinear i (dodecadAffineProjection i p x).val p.1.val = p.1.val :=
  dodecad_affine_recovered_fixed i p x.val ((dodecadAffineStabilizer_mem i p x.val).mp x.prop)

def dodecadKleinProjection (i : HexIndex) (p : DodecadParameters i)
    (j : HexIndex) (hji : j ≠ i) (hj : p.1.val.val.val j = 0) :
    dodecadAffineStabilizer i p →* (hexFiberPermutationHom i j).ker where
  toFun x := ⟨⟨x.val.right,hexPointKernel_fixed_word_other_zero i x.val.right p.1.val p.1.prop
    (dodecadAffineProjection_fixed i p x) j hji hj⟩,by
      let h : hexDoubleZero i j := ⟨p.1.val.val,p.1.val.prop,hj⟩
      have hh : h ≠ 0 := fun hz => p.1.prop (Subtype.ext
        (congrArg (fun u : hexDoubleZero i j => u.val) hz))
      apply hexFiber_fixed_nonzero_kernel i j hji.symm _ h hh
      exact congrArg Subtype.val (dodecadAffineProjection_fixed i p x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Atlas.Codes
