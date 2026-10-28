module
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicRestrictions

/-!
# Fixed quaternion cubic and inverting actions

The standard cubic on Q8 and a reflection are given on the two quaternion generators. The eight-element tables prove inversion and show that the reflection is outer. These fixed actions will be lifted through the actual source conjugation map.

Source: Aschbacher–Smith F.1.12(I)(8), the nonabelian order-96 vertex.
-/

@[expose] public section
open Subgroup
namespace WreathedVertex
abbrev Q8:=QuaternionGroup 2

def inverterMap : Q8→Q8
  | .a i => (QuaternionGroup.xa 2)^i.val
  | .xa i => QuaternionGroup.a 3*(QuaternionGroup.xa 2)^i.val

def quaternionInverter : MulAut Q8 where
  toFun:=inverterMap
  invFun:=inverterMap
  left_inv:=by decide +kernel
  right_inv:=by decide +kernel
  map_mul':=by decide +kernel

theorem quaternionInverter_square : quaternionInverter^2=1 := by
  ext x
  exact (by decide +kernel:∀x:Q8,quaternionInverter (quaternionInverter x)=x) x

theorem quaternionInverter_inverts : quaternionInverter*QuaternionCyclic.quaternionCubic*
    quaternionInverter⁻¹=QuaternionCyclic.quaternionCubic⁻¹ := by
  ext x
  exact (by decide +kernel:∀x:Q8,quaternionInverter
    (QuaternionCyclic.quaternionCubic (quaternionInverter.symm x))=
    QuaternionCyclic.quaternionCubic.symm x) x

theorem quaternionInverter_not_inner :
    quaternionInverter∉(MulAut.conj:Q8→*MulAut Q8).range := by
  rintro ⟨q,hq⟩
  have h:∀q:Q8,∃x:Q8,q*x*q⁻¹≠quaternionInverter x := by decide +kernel
  obtain ⟨x,hx⟩:=h q
  exact hx (DFunLike.congr_fun hq x)

theorem quaternionCubic_order : orderOf QuaternionCyclic.quaternionCubic=3 := by
  have hi:=QuaternionCyclic.extendAutHom_injective
  have h:=orderOf_injective QuaternionCyclic.extendAutHom hi QuaternionCyclic.quaternionCubic
  exact h.symm.trans QuaternionCyclic.cubic_order
end WreathedVertex
