/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ParkerBinaryDetermination.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerFactorSet
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Determination of binary additive forms

Additivity over the binary field reduces vanishing to basis elements and
basis pairs, allowing the Parker factor-set identities to be checked on a basis.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerBinaryDetermination.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed because downstream coordinate proofs unfold them.
-/

@[expose] public section


namespace Atlas.Fischer

variable {V : Type*} [AddCommGroup V] [Module ParkerBit V]

def parkerBinaryLinearMap (f : V → ParkerBit) (hz : f 0 = 0)
    (ha : ∀ x y, f (x + y) = f x + f y) : V →ₗ[ParkerBit] ParkerBit where
  toFun := f
  map_add' := ha
  map_smul' r x := by
    have hr : ∀ s : ParkerBit, s = 0 ∨ s = 1 := by decide
    rcases hr r with rfl | rfl <;> simp [hz]

theorem parkerBinary_eq_zero_of_basis {ι : Type*} (b : Module.Basis ι ParkerBit V)
    (f : V → ParkerBit) (hz : f 0 = 0)
    (ha : ∀ x y, f (x + y) = f x + f y) (hb : ∀ i, f (b i) = 0) :
    ∀ x, f x = 0 := by
  have h : parkerBinaryLinearMap f hz ha = 0 := b.ext (fun i => hb i)
  intro x
  exact congrArg (fun g : V →ₗ[ParkerBit] ParkerBit => g x) h

theorem parkerBinary_biadditive_eq_zero_of_basis {ι : Type*}
    (b : Module.Basis ι ParkerBit V) (f : V → V → ParkerBit)
    (hzl : ∀ y, f 0 y = 0) (hzr : ∀ x, f x 0 = 0)
    (hal : ∀ x x' y, f (x + x') y = f x y + f x' y)
    (har : ∀ x y y', f x (y + y') = f x y + f x y')
    (hb : ∀ i j, f (b i) (b j) = 0) : ∀ x y, f x y = 0 := by
  intro x y
  apply parkerBinary_eq_zero_of_basis b (fun z => f z y) (hzl y)
    (fun z z' => hal z z' y) _ x
  intro i
  exact parkerBinary_eq_zero_of_basis b (f (b i)) (hzr (b i))
    (har (b i)) (hb i) y

end Atlas.Fischer
