module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Transporting centralizers of upper central terms

An isomorphism preserves the upper central series and commutation. Restricting
it therefore identifies the centralizers of corresponding upper central terms.
The coercion theorem records that this restriction preserves marked elements.

Source: the elementary functoriality of the upper central series, expressed by
Mathlib's `Subgroup.comap_upperCentralSeries`.
-/

namespace Subgroup

/-- An isomorphism carries the centralizer of each upper central term onto
its counterpart. -/
public theorem map_centralizer_upperCentralSeries
    {K H : Type*} [Group K] [Group H] (e : K ≃* H) (n : ℕ) :
    (centralizer (upperCentralSeries K n : Set K)).map e.toMonoidHom =
      centralizer (upperCentralSeries H n : Set H) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy' : e.symm y ∈ upperCentralSeries K n := by
      rw [← comap_upperCentralSeries e n]
      change e (e.symm y) ∈ upperCentralSeries H n
      rwa [e.apply_symm_apply]
    simpa only [map_mul, e.apply_symm_apply, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_iff.mp hx (e.symm y) hy')
  · intro y hy
    refine ⟨e.symm y, mem_centralizer_iff.mpr ?_, e.apply_symm_apply y⟩
    intro x hx
    have hx' : e x ∈ upperCentralSeries H n := by
      have hh := hx
      rw [← comap_upperCentralSeries e n] at hh
      exact hh
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_iff.mp hy (e x) hx'

/-- Restrict an isomorphism to the centralizers of the same upper central term. -/
@[expose] public def centralizerUpperCentralSeriesEquiv
    {K H : Type*} [Group K] [Group H] (e : K ≃* H) (n : ℕ) :
    centralizer (upperCentralSeries K n : Set K) ≃*
      centralizer (upperCentralSeries H n : Set H) :=
  (e.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_centralizer_upperCentralSeries e n))

/-- The restricted equivalence agrees with the original isomorphism. -/
public theorem centralizerUpperCentralSeriesEquiv_coe
    {K H : Type*} [Group K] [Group H] (e : K ≃* H) (n : ℕ)
    (x : centralizer (upperCentralSeries K n : Set K)) :
    (centralizerUpperCentralSeriesEquiv e n x : H) = e x := rfl

end Subgroup

