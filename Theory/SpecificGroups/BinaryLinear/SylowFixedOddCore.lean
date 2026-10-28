module
public import Theory.SpecificGroups.BinaryLinear.SylowFixedComponents
public import Theory.GroupAction.SylowFixedInvolutionOddCore
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Odd cores in automorphism centralizers of binary linear Sylow fixers

The pointwise Sylow fixer is inner, and its nonidentity fixed group has
self-centralizing two-core by the concrete transvection-parabolic calculation.
The faithful overgroup transfer preserves the original actors and gives the
odd-core conclusion needed for the PSL₄(2) row of E.6.19, printed p.252.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.OuterCyclic

/-- This applies to every faithful acting overgroup of the inner linear group. -/
theorem sylowFixedInvolution_oddCore_eq_bot {n : ℕ} (hn : n = 4 ∨ n = 5)
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut (LinearGroup n)} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  have hc : center (LinearGroup n) = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    have hh : (slEquivLinear n).symm g ∈ center SL(n,ZMod 2) := by
      apply mem_center_iff.mpr
      intro x
      apply (slEquivLinear n).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        mem_center_iff.mp hg (slEquivLinear n x)
    rw [binary_center_eq_bot (by omega),mem_bot] at hh
    exact mem_bot.mpr ((slEquivLinear n).symm.injective (hh.trans (map_one _).symm))
  apply d.oddCore_eq_bot_of_inner hc (sylow_fixing_inner hn)
  intro S z hz hfix
  have ha : MulAut.conj z ≠ 1 := by
    intro he
    have hz1 := MulAut.conj_injective_of_center_eq_bot hc (he.trans (map_one _).symm)
    simp [hz1] at hz
  have ho := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (sylow_fixed_twoCore hn S (MulAut.conj z) ha hfix)
  rwa [MulAut.fixedSubgroup_conj] at ho
end BinaryLinear.OuterCyclic
