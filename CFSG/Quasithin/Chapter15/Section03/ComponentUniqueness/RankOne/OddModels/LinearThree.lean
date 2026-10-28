module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.Basic
public import Theory.SpecificGroups.PSL3Three.EvenLocals

/-!
# Excluding the ternary linear-three component

The actual matrix model PSL₃(3) is canonically isomorphic to SL₃(3).
Its Sylow two-subgroups are semidihedral of order sixteen. Their only
nontrivial normal elementary subgroup has order two, contradicting the
normal four-group supplied by the reduced configuration.

This proves the L₃(3) branch of Aschbacher--Smith 15.3.43, printed p.1140,
using (b) as well as the subgroup data preceding (e). It does not assert
an exclusion for arbitrary two-locals without the source four-group.
The matrix Sylow calculation is reused from `PSL3Three.EvenLocals`.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

theorem not_linear_three (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (e : L ≃* PSL(3, ZMod 3)) : False := by
  obtain ⟨T, R, hn, he, hc⟩ := normal_four_in_model_sylow c (e.trans Matrix.PSL3Three.equiv.symm)
  let : R.Normal := hn
  let : IsElementaryAbelian 2 R := he
  obtain ⟨a, b, ha, hb, hab, hg⟩ := Matrix.PSL3Three.sylowTwo_generators_SL T
  have hR : R ≠ ⊥ := by intro h; simp [h] at hc
  have h := Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hab hg R hR
  rw [h, Nat.card_zpowers, orderOf_pow, ha] at hc
  norm_num at hc
end CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
