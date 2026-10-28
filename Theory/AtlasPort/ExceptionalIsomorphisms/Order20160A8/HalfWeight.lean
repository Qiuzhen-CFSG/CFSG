module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryWeight
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
Adapted from `Atlas/Algebra/BinaryHalfWeight.lean`.
Half the Hamming weight gives a quadratic form on an even binary code.
Its polar form is the restricted coordinate dot product. Names are localized.
-/

@[expose] public section
namespace Atlas.Order20160A8.HalfWeight
open Atlas.Codes

/-- The half-weight invariant, used only on even binary words below. -/
noncomputable def binaryHalfWeight {ι : Type*} [Fintype ι] (w : ι → Bit) : Bit :=
  (hammingNorm w / 2 : ℕ)

theorem binaryHalfWeight_add {ι : Type*} [Fintype ι] (u v : ι → Bit)
    (hu : 2 ∣ hammingNorm u) (hv : 2 ∣ hammingNorm v)
    (huv : 2 ∣ hammingNorm (u+v)) :
    binaryHalfWeight (u+v)=binaryHalfWeight u+binaryHalfWeight v+binaryDot u v := by
  have hn := binary_weight_add u v
  have he : hammingNorm (u+v)/2+overlap u v=hammingNorm u/2+hammingNorm v/2 := by omega
  have hc := congrArg (fun n : ℕ => (n : Bit)) he
  simp only [Nat.cast_add] at hc
  change binaryHalfWeight (u+v)+(overlap u v : Bit)=binaryHalfWeight u+binaryHalfWeight v at hc
  have hh := congrArg (fun z : Bit => z+(overlap u v : Bit)) hc
  simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,binaryDot_overlap] using hh

@[simp] theorem binaryHalfWeight_zero {ι : Type*} [Fintype ι] :
    binaryHalfWeight (0 : ι → Bit)=0 := by simp [binaryHalfWeight,hammingNorm]

/-- Half-weight is an actual quadratic form on every even binary linear code,
with companion the restricted coordinate dot product. -/
noncomputable def binaryHalfWeightQuadratic {ι : Type*} [Fintype ι]
    (C : Submodule Bit (ι → Bit)) (he : ∀ w : C, 2 ∣ hammingNorm w.val) :
    QuadraticMap Bit C Bit where
  toFun w := binaryHalfWeight w.val
  toFun_smul r w := by
    rcases bit_cases r with hr | hr
    · simp [hr]
    · simp [hr]
  exists_companion' := ⟨binaryDot.restrict C,fun u v => binaryHalfWeight_add _ _ (he u) (he v) (he (u+v))⟩

@[simp] theorem binaryHalfWeightQuadratic_apply {ι : Type*} [Fintype ι]
    (C : Submodule Bit (ι → Bit)) (he : ∀ w : C, 2 ∣ hammingNorm w.val) (w : C) :
    binaryHalfWeightQuadratic C he w=binaryHalfWeight w.val := rfl

theorem binaryHalfWeightQuadratic_polar {ι : Type*} [Fintype ι]
    (C : Submodule Bit (ι → Bit)) (he : ∀ w : C, 2 ∣ hammingNorm w.val) (u v : C) :
    (binaryHalfWeightQuadratic C he).polarBilin u v=binaryDot u.val v.val := by
  change binaryHalfWeight (u.val+v.val)-binaryHalfWeight u.val-binaryHalfWeight v.val=_
  rw [binaryHalfWeight_add _ _ (he u) (he v) (he (u+v))]
  abel

end Atlas.Order20160A8.HalfWeight
