/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryHexadAffinePhases.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryHexadProjection

/-!
# TernaryHexadAffinePhases

Affine fibers of the hexad functional each have 243 elements.
Translation by a chosen preimage identifies each fiber with the linear kernel.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryHexadAffinePhases.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

abbrev TernaryHexadAffinePhase (c : TernarySixWords) (e : ZMod 3) :=
  {a : ternarySupport c.val.val → ZMod 3 // ternaryHexadFunctional c a=e}

def ternaryHexadAffinePhaseEquiv (c : TernarySixWords) (e : ZMod 3) :
    TernaryHexadAffinePhase c e ≃ (ternaryHexadFunctional c).ker := by
  let a := Classical.choose (ternaryHexadFunctional_surjective c e)
  have ha := Classical.choose_spec (ternaryHexadFunctional_surjective c e)
  exact {
    toFun := fun x => ⟨x.val-a,by rw [LinearMap.mem_ker,map_sub,x.prop,ha,sub_self]⟩
    invFun := fun x => ⟨x.val+a,by rw [map_add,(LinearMap.mem_ker.mp x.prop),ha,zero_add]⟩
    left_inv := fun x => Subtype.ext (sub_add_cancel x.val a)
    right_inv := fun x => Subtype.ext (add_sub_cancel_right x.val a)
  }

theorem ternaryHexadAffinePhase_card (c : TernarySixWords) (e : ZMod 3) :
    Nat.card (TernaryHexadAffinePhase c e)=243 := by
  rw [Nat.card_congr (ternaryHexadAffinePhaseEquiv c e)]
  exact ternaryHexadPhase_card c

end Atlas.Codes
