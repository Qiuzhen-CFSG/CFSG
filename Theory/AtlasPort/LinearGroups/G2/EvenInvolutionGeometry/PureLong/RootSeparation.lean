module
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy

/-!
# Separation of the two even G₂ root classes

A nonzero short-root displacement contains the octonion identity. A long-root
displacement cannot contain that identity, and this property is preserved by
all octonion automorphisms. This gives the concrete conjugacy obstruction used
in the pure-long subgroup calculation, without an assumed class table.

Source: Aschbacher–Smith B.4.6(5),(11), printed pp.88–89; explicit root maps
are the licensed ATLAS G₂ formulas imported above.
-/

namespace Atlas.G2.EvenInvolutionGeometry.PureLong
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

public theorem long_conj (g : Model F) {x : Model F}
    (hx : ShortRootProducts.IsLongRootElement x) :
    ShortRootProducts.IsLongRootElement (MulAut.conj g x) := by
  obtain ⟨a, ha, k, rfl⟩ := hx
  refine ⟨a, ha, g * k, ?_⟩
  rw [map_mul, MulAut.mul_apply]

public theorem long_of_conj (g : Model F) {x : Model F}
    (hx : ShortRootProducts.IsLongRootElement (MulAut.conj g x)) :
    ShortRootProducts.IsLongRootElement x := by
  have h := long_conj g⁻¹ hx
  simpa [MulAut.conj_apply, mul_assoc] using h

variable [CharP F 2]

public theorem long_pow_two {x : Model F}
    (hx : ShortRootProducts.IsLongRootElement x) : x ^ 2 = 1 := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  rw [← map_pow, pow_two, rootA_add, CharTwo.add_self_eq_zero, rootA_zero, map_one]

private theorem rootC_displacement {a : F} (ha : a ≠ 0) :
    ∃ v : Carrier F, (rootC a).val v = v + unit := by
  refine ⟨![0,0,0,1,0,0,0,a⁻¹], ?_⟩
  ext i
  fin_cases i <;> simp [rootC, rootCEquiv, rootCLinear, rootCApply, unit,
    CharTwo.neg_eq, CharTwo.add_self_eq_zero, pow_two, ha]

public theorem rootC_not_long {a : F} (ha : a ≠ 0) :
    ¬ ShortRootProducts.IsLongRootElement (rootC a) := by
  rintro ⟨b, _, g, he⟩
  obtain ⟨v,hv⟩ := rootC_displacement ha
  have hv' : g.val ((rootA b).val ((g⁻¹).val v)) = v + unit := by
    rw [he] at hv
    exact hv
  have hh := congrArg (g⁻¹).val hv'
  change g.val.symm (g.val ((rootA b).val (g.val.symm v))) =
    (g⁻¹).val (v + unit) at hh
  rw [LinearEquiv.symm_apply_apply, map_add, automorphism_unit] at hh
  have h3 := congrFun hh 3
  have hz : (1 : F) = 0 := by
    simpa [rootA,rootAEquiv,rootALinear,rootAApply,unit] using h3.symm
  exact one_ne_zero hz

end Atlas.G2.EvenInvolutionGeometry.PureLong
