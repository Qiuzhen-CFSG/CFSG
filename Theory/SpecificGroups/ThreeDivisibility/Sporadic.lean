module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.Representative
public import Mathlib.GroupTheory.GroupAction.Period

/-!
# Three-divisibility in the concrete sporadic carriers

For J₂, HS, He and Ru, a short word has a three-point orbit in the defining
permutation action. Its period divides the element order and hence the group
order. The point evaluations are checked by Lean's kernel. For J₄, the
existing certified matrix word has exact order three.

These proofs use the actual ATLAS carriers and their fixed action conventions.
The imported carrier and certificate modules retain the source data and
attribution. No full group-order or simplicity certification is needed.
Application: Aschbacher--Smith, 1.1.5(3f) and 15.3.34, printed pp.502 and 1134
of `refs/quasithin.pdf`.
-/

public section
namespace Theory.SpecificGroups.ThreeDivisibility

private theorem of_cycle {G X : Type*} [Group G] [MulAction G X] (g : G) (x : X)
    (hc : (g ^ 3) • x = x) (hn : g • x ≠ x) : 3 ∣ Nat.card G := by
  have hper : MulAction.period g x = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp
      (MulAction.pow_smul_eq_iff_period_dvd.mp hc)).resolve_left
        (fun h => hn (MulAction.period_eq_one_iff.mp h))
  exact hper ▸ (MulAction.period_dvd_orderOf g x).trans (orderOf_dvd_natCard g)

theorem j2 : 3 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier := by
  let b : Sporadic.LeechRelated.J2.Carrier :=
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  exact of_cycle b (0 : Fin 100) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem hs : 3 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier := by
  let a : Sporadic.LeechRelated.HS.Carrier :=
    ⟨_, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let b : Sporadic.LeechRelated.HS.Carrier :=
    ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  exact of_cycle (a * b * b * a * b * b * b) (19 : Fin 100)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem held : 3 ∣ Nat.card Held.He :=
  of_cycle (Held.a * Held.b * Held.b) (0 : Fin 2058)
    (by decide +kernel) (by decide +kernel)

theorem rudvalis : 3 ∣ Nat.card Rudvalis.Model := by
  let a := Rudvalis.a
  let b := Rudvalis.b
  exact of_cycle ((a * b * b * a * b * a * b * b * a * b * a * b) ^ 5)
    (0 : Fin 4060) (by decide +kernel) (by decide +kernel)

theorem j4 : 3 ∣ Nat.card Janko4.Model := by
  have h := Janko4.Simplicity.orderOf_primeRepresentative_two
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  exact h ▸ orderOf_dvd_natCard _

end Theory.SpecificGroups.ThreeDivisibility
