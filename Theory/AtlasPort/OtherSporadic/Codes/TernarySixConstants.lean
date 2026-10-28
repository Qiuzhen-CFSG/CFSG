/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernarySixConstants.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolaySupports

/-!
# TernarySixConstants

Weight-six words are neither constant nor equal to their negatives modulo constants.
Their support size and arithmetic over the three-element field prove both assertions.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernarySixConstants.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

theorem ternarySix_not_constant (c : TernarySixWords) (a : ZMod 3) :
    ¬(∀ i,c.val.val i=a) := by
  intro ha
  have he : c.val.val=(fun _ => a) := funext ha
  have hc := c.property
  rw [he] at hc
  by_cases hz : a=0 <;> simp [ternaryWeight,hz] at hc

/-- A nonconstant weight-six word cannot equal its negative modulo constant words. -/
theorem ternarySix_not_negative_shift (c : TernarySixWords) (a : ZMod 3) :
    ¬(∀ i,c.val.val i-(-c.val.val i)=a) := by
  intro h
  have hf : ∀ x y : ZMod 3,x-(-x)=y → x= -y := by decide +kernel
  exact ternarySix_not_constant c (-a) (fun i => hf _ _ (h i))

end Atlas.Codes
