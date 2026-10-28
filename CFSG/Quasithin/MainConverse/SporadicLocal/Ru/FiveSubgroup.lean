module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.FiveSubgroup.Enumeration
public import Theory.GroupTheory.SubgroupClosureFinite

/-!
# A nonabelian subgroup of order 125 in the concrete Rudvalis group

Two explicit words in the degree-4060 ATLAS generators have a central
commutator of exponent five. Collection gives 125 forms, closed under right
multiplication by the generators and their inverses. Closure induction proves
coverage; evaluation at point 0 proves distinctness and noncommutativity.

This supplies the five-subgroup input to `Ru.RankReduction`, without an
ambient order or Sylow assumption. It does not assert the full converse.
Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4; GLS3, Table 5.3r,
p.279, including its 5A row. ATLAS attribution and action conventions are in
`FiveSubgroup/source/README.md` and the underlying model's `PermutationData`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuRank
open Rudvalis Theory.GroupTheory Subgroup FiveCollection

namespace FiveCertificate

private theorem gen_mem (i : Fin 2) : generators i ∈ P :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem x_mem : x ∈ P := gen_mem 0
private theorem y_mem : y ∈ P := gen_mem 1

private theorem z_mem : z ∈ P :=
  P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem y_mem) (P.inv_mem x_mem)) y_mem) x_mem

private theorem reps_mem (t : Coordinates) : reps t ∈ P :=
  P.mul_mem (P.mul_mem (P.pow_mem x_mem _) (P.pow_mem y_mem _)) (P.pow_mem z_mem _)

private theorem reps_injective : Function.Injective reps := by
  intro i j h
  apply point_injective
  rw [← reps_point, ← reps_point, h]

private theorem reps_surjective (g : P) : ∃ i, reps i = g.val :=
  SubgroupEnumeration.closure_range_subset_range_of_transitions
    generators reps (0, 0, 0) next prev (by simp [reps, rep])
      transitions index_inverse g.property

/-- The enumerated subgroup in the original ATLAS carrier has order 125. -/
public theorem card_P : Nat.card P = 125 := by
  let f : Coordinates → P := fun i => ⟨reps i, reps_mem i⟩
  have hi : Function.Injective f := fun i j h => reps_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨i, hi⟩ := reps_surjective g
    exact ⟨i, Subtype.ext hi⟩
  calc
    Nat.card P = Nat.card Coordinates :=
      Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩).symm
    _ = 125 := by simp [Coordinates]

/-- The two generators in this subgroup fail to commute. -/
public theorem not_isMulCommutative_P : ¬ IsMulCommutative P := by
  intro hc
  exact noncommute ((isMulCommutative_iff_of_setLike.mp hc) x x_mem y y_mem)

end FiveCertificate

/-- An unconditional nonabelian order-125 subgroup of the concrete Rudvalis model. -/
public theorem five_subgroup :
    ∃ P : Subgroup Model, Nat.card P = 5 ^ 3 ∧ ¬ IsMulCommutative P :=
  ⟨FiveCertificate.P, FiveCertificate.card_P, FiveCertificate.not_isMulCommutative_P⟩

end CFSG.Quasithin.MainConverse.SporadicLocal.RuRank
