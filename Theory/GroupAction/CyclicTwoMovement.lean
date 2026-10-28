module
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.NormalizerAction
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Odd movement of a cyclic two-subgroup

Conjugation by an odd subgroup has trivial image in the two-group of
automorphisms of a finite cyclic two-group. A cyclic two-subgroup equal
to its commutator with that actor is consequently trivial.
Source application: Aschbacher--Smith 4.3.16, p.618, with core movement
and the separate whole-radical generation identity.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- Odd conjugation cannot generate a nontrivial cyclic two-subgroup. -/
theorem cyclic_twoGroup_eq_bot_of_odd_movement
    (R Y : Subgroup H) [IsCyclic R] (hR : IsPGroup 2 R) (hY : Odd (Nat.card Y))
    (hn : Y ≤ normalizer (R : Set H)) (hm : ⁅R,Y⁆ = R) : R = ⊥ := by
  let f := R.normalizerMonoidHom.comp (inclusion hn)
  have hf (y : Y) : f y = 1 := by
    have hcop := hR.mulAut_of_isCyclic_two.orderOf_coprime
      (Nat.coprime_two_left.mpr hY) (f y)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      ((orderOf_map_dvd f y).trans (orderOf_dvd_natCard y)))
  rw [←hm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro r hr y hy
  have he := congrArg (fun a : MulAut R => (a ⟨r,hr⟩ : H)) (hf ⟨y,hy⟩)
  exact mul_inv_eq_iff_eq_mul.mp he
end Theory.GroupTheory
