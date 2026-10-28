/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryHexadConstantPhases.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryHexadProjection
public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayQuotient

/-!
# TernaryHexadConstantPhases

Codewords constant on a hexad form a set of size nine.
Subtracting the constant word identifies them with the restriction kernel times the scalar field.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryHexadConstantPhases.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

def ternaryHexadConstantCode (c : TernarySixWords) : Submodule (ZMod 3) ternaryGolay where
  carrier := {w | ∃ a : ZMod 3,∀ i : ternarySupport c.val.val,w.val i.val=a}
  zero_mem' := ⟨0,fun _ => rfl⟩
  add_mem' := by
    rintro x y ⟨a,ha⟩ ⟨b,hb⟩
    exact ⟨a+b,fun i => by change x.val i.val+y.val i.val=a+b; rw [ha,hb]⟩
  smul_mem' := by
    rintro a x ⟨b,hb⟩
    exact ⟨a*b,fun i => by change a*x.val i.val=a*b; rw [hb]⟩

def ternaryHexadConstantCodeEquiv (c : TernarySixWords) :
    ternaryHexadConstantCode c ≃ (ternaryRestriction (ternarySupport c.val.val)).ker × ZMod 3 := by
  have hs : (ternarySupport c.val.val).Nonempty := by
    apply Finset.card_pos.mp
    rw [ternarySupport_card,c.prop]; decide
  let i : ternarySupport c.val.val := ⟨hs.choose,hs.choose_spec⟩
  let f (w : ternaryHexadConstantCode c) :
      (ternaryRestriction (ternarySupport c.val.val)).ker :=
    ⟨w.val-(w.val.val i.val) • ternaryOne,by
      apply LinearMap.mem_ker.mpr
      funext j
      obtain ⟨a,ha⟩ := w.prop
      change w.val.val j.val-w.val.val i.val*1=0
      rw [ha,ha]
      ring⟩
  refine
    { toFun := fun w => (f w,w.val.val i.val)
      invFun := fun p => ⟨p.1.val+p.2 • ternaryOne,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨p.2,?_⟩
    intro j
    have hj := congrFun (LinearMap.mem_ker.mp p.1.prop) j
    change p.1.val.val j.val+p.2*1=p.2
    change p.1.val.val j.val=0 at hj
    rw [hj]; ring
  · intro w
    apply Subtype.ext
    change w.val-(w.val.val i.val) • ternaryOne+(w.val.val i.val) • ternaryOne=w.val
    exact sub_add_cancel _ _
  · intro p
    have hi := congrFun (LinearMap.mem_ker.mp p.1.prop) i
    change p.1.val.val i.val=0 at hi
    apply Prod.ext
    · apply Subtype.ext
      change p.1.val+p.2 • ternaryOne-
        ((p.1.val+p.2 • ternaryOne).val i.val) • ternaryOne=p.1.val
      have he : (p.1.val+p.2 • ternaryOne).val i.val=p.2 := by
        change p.1.val.val i.val+p.2*1=p.2
        rw [hi]; ring
      rw [he,add_sub_cancel_right]
    · change p.1.val.val i.val+p.2*1=p.2
      rw [hi]; ring

theorem ternaryHexadConstantCode_card (c : TernarySixWords) :
    Nat.card (ternaryHexadConstantCode c)=9 := by
  rw [Nat.card_congr (ternaryHexadConstantCodeEquiv c),Nat.card_prod,
    ternaryHexadRestriction_kernel_card]
  norm_num

end Atlas.Codes
