module
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
/-!
# The outer A6–C3 configuration has nonperfect two-residual

Modulo the literal A6 factor, the cubic factor and the outer cyclic generator
form a solvable group. A perfect two-residual would therefore lie in A6.
Every element of the disjoint cubic factor already lies in the two-residual,
which is impossible. This uses only the original marked group configuration;
no module decomposition or assertion about the outer generator's order is needed.

Source: Aschbacher–Smith, exclusion of B.5.6(4) in B.6.9, pp.105 and 116.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.OuterSixThreeShape
variable {D : Type*} [Group D] (c : OuterSixThreeShape D)

/-- The quotient by the original A6 factor is solvable. -/
theorem quotient_first_solvable : letI := c.first_normal; Group.IsSolvable (D ⧸ c.first) := by
  let := c.first_normal
  let := c.second_normal
  let q := QuotientGroup.mk' c.first
  let : Group.IsSolvable c.second :=
    Group.isSolvable_of_isSolvable_injective (f := c.secondEquiv.toMonoidHom) c.secondEquiv.injective
  let : Group.IsSolvable (c.second.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective c.second)
  let : Group.IsSolvable ((zpowers c.element).map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective (zpowers c.element))
  have hg : c.second.map q ⊔ (zpowers c.element).map q = ⊤ := by
    have he := congrArg (map q) c.generates
    simpa [q, Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  exact Group.isSolvable_of_normal_sup_eq_top _ _ hg

/-- The literal cubic factor lies in the two-residual. -/
theorem second_le_two_residual : c.second ≤ pResidual 2 D := by
  have hp : IsPGroup 3 c.second := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp)
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  have hh := hp.orderOf_coprime (by decide : Nat.Coprime 3 2) (⟨x,hx⟩ : c.second)
  rw [← Subgroup.orderOf_coe] at hh
  exact hh.symm

include c in
/-- The outer configuration is incompatible with a perfect two-residual. -/
theorem not_perfect_two_residual : ¬ Group.IsPerfect (pResidual 2 D) := by
  intro hp
  let := hp
  let := c.first_normal
  let := c.quotient_first_solvable
  have hr : pResidual 2 D ≤ c.first := le_of_isPerfect_of_solvable_quotient _ _
  have hb : c.second = ⊥ := bot_unique fun x hx =>
    c.factors_disjoint.le_bot ⟨hr (c.second_le_two_residual hx),hx⟩
  have hc : Nat.card c.second = 3 := by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp
  rw [hb, Nat.card_unique] at hc
  omega
end CFSG.Quasithin.ChapterB.OuterSixThreeShape
