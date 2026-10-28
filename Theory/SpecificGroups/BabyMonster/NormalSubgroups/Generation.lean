module

public import Theory.SpecificGroups.BabyMonster.Perfect
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# Normal generation in the Baby Monster presentation

A normal subgroup containing one canonical generator contains all of them:
in the quotient, the adjacent Coxeter relation and the involution relation
force the next generator to be trivial. Connectivity of the `Y₄₃₃` diagram
then gives normal generation. This uses only the relations of §3.1 of
Breuer–Magaard–Wilson (2019), https://arxiv.org/abs/1902.07758.

The fixed generator centralizer is also named here for the independent local
calculations used in the normal-subgroup argument.
-/

public section
namespace BabyMonster

/-- The centralizer of the first canonical involution. -/
@[expose] def generatorCentralizer : Subgroup Carrier :=
  Subgroup.centralizer {generator 0}


private theorem generator_image_eq_one_iff {G : Type*} [Group G]
    (f : Carrier →* G) (i : Generator) :
    f (generator i) = 1 ↔ f (generator 0) = 1 := by
  have hs (j : Generator) : f (generator j) ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg f (generator_sq j)
  have hedge (j k : Generator) (hjk : (j, k) ∈ edges) :
      f (generator j) = 1 ↔ f (generator k) = 1 := by
    have hjk' : j < k := by
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hjk
      rcases hjk with h | h | h | h | h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> decide
    have hp : (f (generator j) * f (generator k)) ^ 3 = 1 := by
      simpa only [coxeterExponent, if_pos hjk, map_pow, map_mul, map_one] using
        congrArg f (generator_pair j k hjk')
    constructor
    · intro hj
      rw [hj, one_mul] at hp
      simpa only [pow_succ, hs k, one_mul] using hp
    · intro hk
      rw [hk, mul_one] at hp
      simpa only [pow_succ, hs j, one_mul] using hp
  have h01 := hedge 0 1 (by decide)
  have h12 := hedge 1 2 (by decide)
  have h23 := hedge 2 3 (by decide)
  have h34 := hedge 3 4 (by decide)
  have h45 := hedge 4 5 (by decide)
  have h56 := hedge 5 6 (by decide)
  have h67 := hedge 6 7 (by decide)
  have h48 := hedge 4 8 (by decide)
  have h89 := hedge 8 9 (by decide)
  have h910 := hedge 9 10 (by decide)
  fin_cases i <;> grind

/-- Killing any one canonical generator kills the whole presented group. -/
theorem hom_eq_one_of_generator_eq_one {G : Type*} [Group G]
    (f : Carrier →* G) (i : Generator) (hi : f (generator i) = 1) : f = 1 := by
  apply hom_ext
  intro j
  exact (generator_image_eq_one_iff f j).mpr ((generator_image_eq_one_iff f i).mp hi)

/-- A normal subgroup containing any canonical generator is the whole group. -/
theorem normal_eq_top_of_generator_mem (N : Subgroup Carrier) [N.Normal]
    (i : Generator) (hi : generator i ∈ N) : N = ⊤ := by
  have hf := hom_eq_one_of_generator_eq_one (QuotientGroup.mk' N) i
    ((QuotientGroup.eq_one_iff _).mpr hi)
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf x

/-- Each canonical generator normally generates the fixed carrier. -/
theorem normalClosure_generator (i : Generator) :
    Subgroup.normalClosure ({generator i} : Set Carrier) = ⊤ :=
  normal_eq_top_of_generator_mem _ i (Subgroup.subset_normalClosure (by simp))

end BabyMonster
