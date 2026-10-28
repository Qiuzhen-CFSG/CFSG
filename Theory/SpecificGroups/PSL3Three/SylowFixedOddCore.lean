module
public import Theory.SpecificGroups.PSL3Three.SylowFixersInner
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer
public import Theory.GroupAction.SylowFixedInvolutionOddCore
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The PSL₃(3) actor centralizer in E.6.19

Full Sylow pointwise innerness gives the inner actor. The original fixed
subgroup of every inner involution is the concrete GL₂(3), whose two-core
is self-centralizing. The faithful-overgroup transfer then proves the
odd-core conclusion on the original acting group.

Source: Aschbacher–Smith E.6.19, printed p.252, using the inner case of
16.1.5(1), p.1171, and the full pointwise-fixer calculation of E.6.8(5).
-/

public section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Three

/-- Triviality of the odd core for the literal faithful acting overgroup. -/
theorem sylowFixedInvolution_oddCore_eq_bot
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut PSL} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  have hc : center PSL = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL
  apply d.oddCore_eq_bot_of_inner hc sylow_fixed_inner
  intro S z hz _
  have ha : orderOf (MulAut.conj z) = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot hc z).trans hz
  have ho := pPrimeCore_eq_bot_of_equiv
    (innerInvolutoryAutFixedEquiv (MulAut.conj z) ha ⟨z,rfl⟩)
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2
      GeneralLinearGroup.three_centralizer_twoCore_le)
  rwa [MulAut.fixedSubgroup_conj] at ho
end Matrix.PSL3Three
