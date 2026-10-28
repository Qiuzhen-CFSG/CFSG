module
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
/-!
# No characteristic-two SL₃ embedding in finite characteristic-two SL₂

The upper-unitriangular group in SL₃ contains an element of order four.
Every two-subgroup of a finite characteristic-two SL₂ group has exponent
two. Restricting an alleged embedding to that concrete unitriangular group
gives the contradiction. No order comparison between fields is needed.

Source: GLS4, Chapter4, Lemma3.5(a), and the standard UT₃ matrix calculation.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open Matrix.PSL3Even.UnipotentGeometry
variable {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [CharP F 2]

/-- A characteristic-two SL₃ cannot embed in finite characteristic-two SL₂. -/
theorem not_injective_linearThree_to_binaryLinearTwo
    (f : SL(3,F) →* SL(2,E)) : ¬ Function.Injective f := by
  intro hf
  let g := f.comp (specialLinear F)
  have hg : Function.Injective g := hf.comp (specialLinear_injective F)
  have hU : IsPGroup 2 (U F) := by
    intro x
    refine ⟨2,?_⟩
    have hx : (x ^ 2) ^ 2 = 1 := (square_eq_one_iff F _).mpr
      (Or.inl (by simp [pow_two,CharTwo.add_self_eq_zero]))
    simpa only [← pow_mul, show 2 * 2 = 2 ^ 2 from rfl] using hx
  have hP : IsPGroup 2 g.range := hU.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  let x : U F := ⟨1,1,0⟩
  have hx : (g.rangeRestrict x) ^ 2 = 1 := twoSubgroup_pow_two g.range hP _
  have hxg : g x ^ 2 = 1 := congrArg g.range.subtype hx
  have hx' : x ^ 2 = 1 := hg (by simpa only [map_pow,map_one] using hxg)
  have h := (square_eq_one_iff F x).mp hx'
  simp [x] at h
end Matrix.SpecialLinearGroup
