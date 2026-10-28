module

public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The order-four obstruction for characteristic-two PSL₂

A Sylow two-subgroup of SL₂ is the additive field. Thus every element of
2-power order has square one. The actual SL₂–PSL₂ quotient equivalence
transports the resulting exclusion of order four to PSL₂.

This supplies the rank-one side of the model comparison needed after the
strict-ratio sieve in B.4.2. It applies at every finite characteristic-two
field, including even field exponents; no group-order formula is needed.

Source: the upper-unipotent Sylow calculation for SL₂, applied to the
B.4.2 alternatives in Aschbacher–Smith 13.8.16(1), printed p.952.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

/-- No element of the actual special linear group has order four. -/
theorem sl_order_ne_four {F : Type*} [Field F] [Finite F] [CharP F 2] (x : SL(2,F)) : orderOf x ≠ 4 := by
  intro ho
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by rw [Nat.card_zpowers, ho]; norm_num)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S
  let y : S := ⟨x, hS (mem_zpowers x)⟩
  have hy : y ^ 2 = 1 := by
    apply e.symm.injective
    rw [map_pow, map_one]
    change Multiplicative.ofAdd (2 • Multiplicative.toAdd (e.symm y)) = Multiplicative.ofAdd 0
    rw [CharTwo.two_nsmul]
  have hx : x ^ 2 = 1 := congrArg Subtype.val hy
  have hd := orderOf_dvd_of_pow_eq_one hx
  rw [ho] at hd
  norm_num at hd

/-- The projective quotient in characteristic two has the same obstruction. -/
theorem psl_order_ne_four {F : Type*} [Field F] [Finite F] [CharP F 2]
    (x : PSL(2,F)) : orderOf x ≠ 4 := by
  intro hx
  let e := Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)
  exact sl_order_ne_four (e.symm x) ((e.symm.orderOf_eq x).trans hx)

/-- A single actual element of order four suffices to exclude a proposed
multiplicative equivalence with PSL₂ over a finite characteristic-two field. -/
theorem not_equiv_psl_of_order_four {F E : Type*}
    [Field F] [Finite F] [CharP F 2] [Group E]
    (g : E) (hg : orderOf g = 4) : ¬ Nonempty (PSL(2,F) ≃* E) := by
  rintro ⟨e⟩
  exact psl_order_ne_four (e.symm g) ((e.symm.orderOf_eq g).trans hg)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
